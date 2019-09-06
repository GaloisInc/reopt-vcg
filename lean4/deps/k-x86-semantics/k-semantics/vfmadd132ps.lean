def vfmadd132ps1 : instruction :=
  definst "vfmadd132ps" $ do
    pattern fun (v_2529 : reg (bv 128)) (v_2530 : reg (bv 128)) (v_2531 : reg (bv 128)) => do
      v_4190 <- getRegister v_2531;
      v_4193 <- getRegister v_2529;
      v_4197 <- getRegister v_2530;
      setRegister (lhs.of_reg v_2531) (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_4190 0 32) 24 8) (MInt2Float (extract v_4193 0 32) 24 8)) (MInt2Float (extract v_4197 0 32) 24 8)) 32) (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_4190 32 64) 24 8) (MInt2Float (extract v_4193 32 64) 24 8)) (MInt2Float (extract v_4197 32 64) 24 8)) 32) (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_4190 64 96) 24 8) (MInt2Float (extract v_4193 64 96) 24 8)) (MInt2Float (extract v_4197 64 96) 24 8)) 32) (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_4190 96 128) 24 8) (MInt2Float (extract v_4193 96 128) 24 8)) (MInt2Float (extract v_4197 96 128) 24 8)) 32))));
      pure ()
    pat_end;
    pattern fun (v_2543 : reg (bv 256)) (v_2544 : reg (bv 256)) (v_2545 : reg (bv 256)) => do
      v_4238 <- getRegister v_2545;
      v_4241 <- getRegister v_2543;
      v_4245 <- getRegister v_2544;
      setRegister (lhs.of_reg v_2545) (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_4238 0 32) 24 8) (MInt2Float (extract v_4241 0 32) 24 8)) (MInt2Float (extract v_4245 0 32) 24 8)) 32) (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_4238 32 64) 24 8) (MInt2Float (extract v_4241 32 64) 24 8)) (MInt2Float (extract v_4245 32 64) 24 8)) 32) (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_4238 64 96) 24 8) (MInt2Float (extract v_4241 64 96) 24 8)) (MInt2Float (extract v_4245 64 96) 24 8)) 32) (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_4238 96 128) 24 8) (MInt2Float (extract v_4241 96 128) 24 8)) (MInt2Float (extract v_4245 96 128) 24 8)) 32) (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_4238 128 160) 24 8) (MInt2Float (extract v_4241 128 160) 24 8)) (MInt2Float (extract v_4245 128 160) 24 8)) 32) (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_4238 160 192) 24 8) (MInt2Float (extract v_4241 160 192) 24 8)) (MInt2Float (extract v_4245 160 192) 24 8)) 32) (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_4238 192 224) 24 8) (MInt2Float (extract v_4241 192 224) 24 8)) (MInt2Float (extract v_4245 192 224) 24 8)) 32) (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_4238 224 256) 24 8) (MInt2Float (extract v_4241 224 256) 24 8)) (MInt2Float (extract v_4245 224 256) 24 8)) 32))))))));
      pure ()
    pat_end;
    pattern fun (v_2526 : Mem) (v_2524 : reg (bv 128)) (v_2525 : reg (bv 128)) => do
      v_10216 <- getRegister v_2525;
      v_10219 <- evaluateAddress v_2526;
      v_10220 <- load v_10219 16;
      v_10224 <- getRegister v_2524;
      setRegister (lhs.of_reg v_2525) (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_10216 0 32) 24 8) (MInt2Float (extract v_10220 0 32) 24 8)) (MInt2Float (extract v_10224 0 32) 24 8)) 32) (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_10216 32 64) 24 8) (MInt2Float (extract v_10220 32 64) 24 8)) (MInt2Float (extract v_10224 32 64) 24 8)) 32) (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_10216 64 96) 24 8) (MInt2Float (extract v_10220 64 96) 24 8)) (MInt2Float (extract v_10224 64 96) 24 8)) 32) (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_10216 96 128) 24 8) (MInt2Float (extract v_10220 96 128) 24 8)) (MInt2Float (extract v_10224 96 128) 24 8)) 32))));
      pure ()
    pat_end;
    pattern fun (v_2535 : Mem) (v_2538 : reg (bv 256)) (v_2539 : reg (bv 256)) => do
      v_10260 <- getRegister v_2539;
      v_10263 <- evaluateAddress v_2535;
      v_10264 <- load v_10263 32;
      v_10268 <- getRegister v_2538;
      setRegister (lhs.of_reg v_2539) (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_10260 0 32) 24 8) (MInt2Float (extract v_10264 0 32) 24 8)) (MInt2Float (extract v_10268 0 32) 24 8)) 32) (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_10260 32 64) 24 8) (MInt2Float (extract v_10264 32 64) 24 8)) (MInt2Float (extract v_10268 32 64) 24 8)) 32) (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_10260 64 96) 24 8) (MInt2Float (extract v_10264 64 96) 24 8)) (MInt2Float (extract v_10268 64 96) 24 8)) 32) (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_10260 96 128) 24 8) (MInt2Float (extract v_10264 96 128) 24 8)) (MInt2Float (extract v_10268 96 128) 24 8)) 32) (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_10260 128 160) 24 8) (MInt2Float (extract v_10264 128 160) 24 8)) (MInt2Float (extract v_10268 128 160) 24 8)) 32) (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_10260 160 192) 24 8) (MInt2Float (extract v_10264 160 192) 24 8)) (MInt2Float (extract v_10268 160 192) 24 8)) 32) (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_10260 192 224) 24 8) (MInt2Float (extract v_10264 192 224) 24 8)) (MInt2Float (extract v_10268 192 224) 24 8)) 32) (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_10260 224 256) 24 8) (MInt2Float (extract v_10264 224 256) 24 8)) (MInt2Float (extract v_10268 224 256) 24 8)) 32))))))));
      pure ()
    pat_end
