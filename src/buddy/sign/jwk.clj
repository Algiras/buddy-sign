(ns buddy.sign.jwk
  (:require [buddy.core.codecs :as codecs]
            [buddy.core.codecs.base64 :as c64]
            [clojure.string :as str]
            [buddy.sign.jwk.eliptic-curves :refer [curves]]
            [buddy.sign.jwt :as jwt]
            [buddy.sign.jwe :as jwe]
            [clojure.spec :as s]
            [cheshire.core :as json])
  (:import [org.apache.commons.codec.binary Base64]
           [java.security.spec RSAPublicKeySpec RSAPrivateKeySpec RSAPrivateCrtKeySpec ECPoint ECPrivateKeySpec ECPublicKeySpec]
           [javax.crypto.spec SecretKeySpec]
           [java.security.interfaces RSAPublicKey RSAPrivateKey]
           [java.security KeyFactory]))

; UPDATE keys to work with normal JSON
; No JOSE Header implementation

; https://www.rfc-editor.org/rfc/pdfrfc/rfc7518.txt.pdf
(s/def ::kid (s/and string? (comp not empty?)))

(def RSA "RSA")
(def EC "EC")
(def oct "oct")
(s/def ::kty #{RSA EC oct})

;; missing: "enc"
(s/def ::use #{"sig" "enc"})

(s/def ::key_op #{"sign" "verify" "encrypt" "decrypt" "wrapKey" "unwrapKey" "deriveKey" "deriveBits"})
(s/def ::key_ops (s/coll-of ::key_op))

;; missing: "HS384" "RS384" "ES384"  "PS384" "none"
(s/def ::alg #{"HS256" "HS512" "RS256" "RS512" "ES256" "ES512" "PS256" "PS512" "HS384" "RS384" "ES384" "PS384" "none"})

;; missing: support for certificates x5u,x5c,x5t,x5t#S256
(s/def ::jwk (s/keys :req-un [::kty]
                     :opt-un [::alg ::use ::kid ::key_ops]))

(s/def ::encoded-string (s/and string? (comp not empty?) #(Base64/isArrayByteBase64 (.getBytes %))))

(s/def ::k ::encoded-string)
(s/def ::kty-oct-key (s/and ::jwk (s/keys :req-un [::k])))

; Elliptic Curve
; missing: for starting version only supports rfc7518 defined curves
(s/def ::crv (set (map name (keys curves))))
(s/def ::x ::encoded-string)
(s/def ::y ::encoded-string)
(s/def ::d ::encoded-string)

(s/def ::kty-EC-public-key (s/and ::jwk (s/keys :req-un [::crv ::x ::y])))

(s/def ::kty-EC-private-key (s/and ::kty-EC-public-key (s/keys :req-un [::d])))

; RSA
(s/def ::n ::encoded-string)
(s/def ::e ::encoded-string)
(s/def ::kty-RSA-public-key (s/and ::jwk (s/keys :req-un [::n ::e])))

(s/def ::d ::encoded-string)
(s/def ::p ::encoded-string)
(s/def ::q ::encoded-string)
(s/def ::dp ::encoded-string)
(s/def ::dq ::encoded-string)
(s/def ::qi ::encoded-string)

(s/def ::kty-RSA-private-key (s/and ::kty-RSA-public-key (s/keys :req-un [::d])))

(s/def ::kty-RSA-private-certified-key (s/and ::kty-RSA-private-key (s/keys :req-un [::p ::q ::dp ::dq ::qi])))

(s/def ::keys (s/and (s/+ (s/or ::kty-oct-key ::kty-EC-public-key ::kty-EC-private-key ::kty-RSA-public-key ::kty-RSA-private-key ::kty-RSA-private-certified-key))
                       #(if (> (count %) 1) (->> % (map :kid) (apply distinct?)) true)))
(s/def ::jwks (s/keys :req-un [::keys]))

(defn ^{:private true} base64Url->BigInt [param]
  (new BigInteger 1 (c64/decode param)))

(defmulti ^{:private true} jwk->keys :kty)

(defmethod ^{:private true} jwk->keys RSA [jwk]
  (let [modulus (base64Url->BigInt (:n jwk))
        exponent (base64Url->BigInt (:e jwk))
        private-exponent (base64Url->BigInt (:d jwk))
        first-prime-factor (base64Url->BigInt (:p jwk))
        second-prime-factor (base64Url->BigInt (:q jwk))
        first-factor-cert-exponent (base64Url->BigInt (:dp jwk))
        second-factor-cert-exponent (base64Url->BigInt (:dq jwk))
        first-cert-coefficient (base64Url->BigInt (:qi jwk))
        key-factory (KeyFactory/getInstance RSA)]
    (cond
      (s/valid? ::kty-RSA-private-certified-key jwk) {:private (.generatePrivate key-factory
                                                                                  (new RSAPrivateCrtKeySpec modulus exponent private-exponent first-prime-factor
                                                                                       second-prime-factor first-factor-cert-exponent second-factor-cert-exponent first-cert-coefficient))
                                                      :public (.generatePublic key-factory (new RSAPublicKeySpec modulus exponent))}

      (s/valid? ::kty-RSA-private-key jwk) {:private (.generatePrivate key-factory (new RSAPrivateKeySpec modulus private-exponent))
                                            :public (.generatePublic key-factory (new RSAPublicKeySpec modulus exponent))}

      (s/valid? ::kty-RSA-public-key jwk) {:public (.generatePublic (KeyFactory/getInstance RSA) (new RSAPublicKeySpec modulus exponent))})))

(defmethod ^{:private true} jwk->keys EC [jwk]
  (let [curve (curves (keyword (:crv jwk)))
        x (base64Url->BigInt (:x jwk))
        y (base64Url->BigInt (:y jwk))
        d (base64Url->BigInt (:d jwk))
        key-factory (KeyFactory/getInstance EC)]
    (cond
      (s/valid? ::kty-EC-private-key jwk) {:private (.generatePrivate key-factory (new ECPrivateKeySpec d curve))
                                           :public (.generatePublic key-factory (new ECPublicKeySpec (new ECPoint x y) curve))}
      (s/valid? ::kty-EC-public-key jwk) {:public (.generatePublic key-factory (new ECPublicKeySpec (new ECPoint x y) curve))})))

(defmethod ^{:private true} jwk->keys oct [jwk]
  (when (s/valid? ::kty-oct-key jwk)
    (let [octet-sequence (c64/decode (:k jwk))
          key (new SecretKeySpec octet-sequence "AES")]
      {:public key :private key})))

(defmethod ^{:private true} jwk->keys :default [x] {:public nil :private nil})

(defn ^{:private true} jwk->wrap-keys [jwk]
  (assoc jwk :keys (jwk->keys jwk)))

(defn jwks->key-set [jwks]
  (when (s/valid? ::jwks jwks)
    (assoc jwks :keys (map jwk->keys (:keys jwks)))))

(defn ^:private get-matching-jwks-key [kid use key-set]
  (let [used-keysets (filter #(= (:use %) use) (:keys key-set))]
    (->> used-keysets
               (filter #(= (:kid %) kid))
               (#(or (first %) (first keys))))))

(defn sign
  ([claims key-set kid] (sign claims key-set kid {}))
  ([claims key-set kid opts]
   {:pre [(map? claims)]}
   (if (and (:sub claims) (:aud claims) (:iss claims))
     (let [key (get-matching-jwks-key kid "sig" key-set)
           alg (key :alg)
           p-key (get-in key [:keys :public])
           m-opts (merge opts {:alg (keyword (str/lower-case alg))})]
         (jwt/sign claims key m-opts))
     (throw (ex-info "Message is missing :sub or :aud or :iss claims"
                     {:type :validation :cause :signature})))))

(defn unsign
  ([message key-set] (unsign message key-set {}))
  ([message key-set opts]
   (let [kid (:kid (jwe/decode-header message))
         key (get-matching-jwks-key kid "sig" key-set)
         alg (keyword (str/lower-case (key :alg)))
         p-key (get-in key [:keys :public])
         m-opts (merge opts {:alg alg :req-subject true})]
     (jwt/unsign message p-key m-opts))))

; Generator for all key JAVA classes
; Generate keys from java keys
; Rewrite spec to be concise
