#include <stdio.h>
#include <string.h>
#include <stdbool.h>
#include <glib.h>


#include <caml/mlvalues.h>
#include <caml/callback.h>
#include <caml/memory.h>


#include <openssl/rand.h>
#include <openssl/err.h>
#include <openssl/bio.h>
#include <openssl/pem.h>
#include <openssl/rsa.h>
#include <openssl/ec.h>


#include "config.h"


EC_KEY* newEC() {
  int eccgrp = OBJ_txt2nid("prime256v1");
  EC_KEY *key = EC_KEY_new_by_curve_name(eccgrp);
  EC_KEY_set_asn1_flag(key, OPENSSL_EC_NAMED_CURVE);
  return key;
}

EC_KEY** newEC0(int i) {
  EC_KEY* key1 = newEC();
  EC_KEY** key2 = &key1;
  return key2;
}

int loadPrivateKey(unsigned int id, EC_KEY** priv) {
  if (DEBUG) { printf(KYEL "loading private key" KNRM "\n"); }

  gchar *num = g_strdup_printf("%i", id);
  gchar *pr = g_strconcat ("somekeys/ec256_private", num, NULL);
  if (DEBUG) { printf(KYEL "opening file: %s" KNRM "\n", pr); }
  FILE * fpr = fopen (pr, "rb");

  if (fpr == NULL) {
    printf(KYEL "Unable to open file %s" KNRM "\n", pr);
    return 1;
  }

  EVP_PKEY *pkey = EVP_PKEY_new();
  pkey = PEM_read_PrivateKey(fpr, &pkey, NULL, NULL);
  *priv = EVP_PKEY_get1_EC_KEY(pkey);
  fclose(fpr);
  if (DEBUG) { printf(KYEL "loaded private key from %s" KNRM "\n", pr); }

  // free the pkey
  EVP_PKEY_free(pkey);

  return 0;
}

int loadPrivateKey0(value id, EC_KEY** priv) {
  int i = loadPrivateKey(Int_val(id),priv);
  return i;
}


int loadPublicKey(unsigned int id, EC_KEY** pub) {
  if (DEBUG) { printf(KYEL "loading public key" KNRM "\n"); }

  gchar *num = g_strdup_printf("%i", id);
  gchar *pb = g_strconcat ("somekeys/ec256_public", num, NULL);
  FILE * fpb = fopen (pb, "rb");

  if (fpb == NULL) {
    printf(KYEL "Unable to open file %s" KNRM "\n", pb);
    return 1;
  }

  EVP_PKEY *pkey = EVP_PKEY_new();
  pkey = PEM_read_PUBKEY(fpb, &pkey, NULL, NULL);
  *pub = EVP_PKEY_get1_EC_KEY(pkey);
  fclose(fpb);
  if (DEBUG) { printf(KYEL "loaded public key from %s" KNRM "\n", pb); }

  // free the pkey
  EVP_PKEY_free(pkey);

  return 0;
}

int loadPublicKey0(value id, EC_KEY** pub) {
  int i = loadPublicKey(Int_val(id),pub);
  return i;
}


// 'len' is the length of 'text'
void signText(char* text, int len, EC_KEY* priv, unsigned char sign[SIGN_LEN]) {
  if (DEBUG) { printf(KCYN "signing text using EC" KNRM "\n"); }
  unsigned int signLen;
  unsigned char hash[SHA256_DIGEST_LENGTH];

  if (DEBUG) { printf(KCYN "generating hash" KNRM "\n"); }
  if (!SHA256 ((const unsigned char *)text, len, hash)){
    printf(KCYN "SHA1 failed" KNRM "\n");
    exit(0);
  }

  if (DEBUG) { printf(KCYN "generating signature" KNRM "\n"); }
  if (!ECDSA_sign (NID_sha256, hash, SHA256_DIGEST_LENGTH, sign, &signLen, priv)) {
    printf(KCYN "ECDSA_sign failed" KNRM "\n");
    exit(0);
  }
  if (DEBUG) { printf(KCYN "signed(%d)" KNRM "\n", signLen); }
}


bool verifyText(char* text, int len, EC_KEY* pub, unsigned char sign[SIGN_LEN]) {
  if (DEBUG) { printf(KCYN "verifying text using EC" KNRM "\n"); }
  unsigned int signLen = SIGN_LEN;
  unsigned char hash[SHA256_DIGEST_LENGTH];

  if (!SHA256 ((const unsigned char *)text, len, hash)){
    printf(KCYN "SHA1 failed" KNRM "\n");
    exit(0);
  }

  bool b = ECDSA_verify (NID_sha256, hash, SHA256_DIGEST_LENGTH, sign, signLen, pub);

  return b;
}

void signTextTest(EC_KEY* priv, unsigned char sign[SIGN_LEN]) {
  char* s = "foo";
  int len = 3;
  signText(s,len,priv,sign);
}

gchar* signTextTest0(EC_KEY* priv) {
  //gchar* sign = String_val(sgn);
  gchar * sign = (gchar *)malloc(sizeof(gchar) * SIGN_LEN);
  gchar* s = "foo";
  int len = 3;

  //--
  priv = newEC();
  loadPrivateKey(0,&priv);
  //--

  signText(s,len,priv,sign);
  return sign;
}

value caml_test(value v) {
  int selfid = 0;
  EC_KEY* priv = newEC();
  EC_KEY* pub  = newEC();
  if (DEBUG) { printf(KCYN "loading private key" KNRM "\n"); }
  loadPrivateKey(selfid,&priv);
  if (DEBUG) { printf(KCYN "loading public key" KNRM "\n"); }
  loadPublicKey(selfid,&pub);

  unsigned char sign[SIGN_LEN];
  char* s = "foo";
  int len = 3;
  signText(s,len,priv,sign);
  bool b = verifyText(s,len,pub,sign);

  if (DEBUG) { printf(KCYN "result:%d" KNRM "\n", b); }
  return Val_int(0);
}

/*
int main (int argc, char** argv) {
  caml_test(Val_int(0));
  return 0;
}
*/
