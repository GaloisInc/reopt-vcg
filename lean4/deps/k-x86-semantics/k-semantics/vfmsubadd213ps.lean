def vfmsubadd213ps1 : instruction :=
  definst "vfmsubadd213ps" $ do
    pattern fun (v_3012 : reg (bv 128)) (v_3013 : reg (bv 128)) (v_3014 : reg (bv 128)) => do
      v_6426 <- getRegister v_3013;
      v_6429 <- getRegister v_3014;
      v_6433 <- getRegister v_3012;
      setRegister (lhs.of_reg v_3014) (concat (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_6426 0 32) 24 8) (MInt2Float (extract v_6429 0 32) 24 8)) (MInt2Float (extract v_6433 0 32) 24 8)) 32) (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_6426 32 64) 24 8) (MInt2Float (extract v_6429 32 64) 24 8)) (MInt2Float (extract v_6433 32 64) 24 8)) 32)) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_6426 64 96) 24 8) (MInt2Float (extract v_6429 64 96) 24 8)) (MInt2Float (extract v_6433 64 96) 24 8)) 32) (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_6426 96 128) 24 8) (MInt2Float (extract v_6429 96 128) 24 8)) (MInt2Float (extract v_6433 96 128) 24 8)) 32)));
      pure ()
    pat_end;
    pattern fun (v_3024 : reg (bv 256)) (v_3025 : reg (bv 256)) (v_3026 : reg (bv 256)) => do
      v_6474 <- getRegister v_3025;
      v_6477 <- getRegister v_3026;
      v_6481 <- getRegister v_3024;
      setRegister (lhs.of_reg v_3026) (concat (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_6474 0 32) 24 8) (MInt2Float (extract v_6477 0 32) 24 8)) (MInt2Float (extract v_6481 0 32) 24 8)) 32) (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_6474 32 64) 24 8) (MInt2Float (extract v_6477 32 64) 24 8)) (MInt2Float (extract v_6481 32 64) 24 8)) 32)) (concat (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_6474 64 96) 24 8) (MInt2Float (extract v_6477 64 96) 24 8)) (MInt2Float (extract v_6481 64 96) 24 8)) 32) (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_6474 96 128) 24 8) (MInt2Float (extract v_6477 96 128) 24 8)) (MInt2Float (extract v_6481 96 128) 24 8)) 32)) (concat (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_6474 128 160) 24 8) (MInt2Float (extract v_6477 128 160) 24 8)) (MInt2Float (extract v_6481 128 160) 24 8)) 32) (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_6474 160 192) 24 8) (MInt2Float (extract v_6477 160 192) 24 8)) (MInt2Float (extract v_6481 160 192) 24 8)) 32)) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_6474 192 224) 24 8) (MInt2Float (extract v_6477 192 224) 24 8)) (MInt2Float (extract v_6481 192 224) 24 8)) 32) (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_6474 224 256) 24 8) (MInt2Float (extract v_6477 224 256) 24 8)) (MInt2Float (extract v_6481 224 256) 24 8)) 32)))));
      pure ()
    pat_end;
    pattern fun (v_3009 : Mem) (v_3007 : reg (bv 128)) (v_3008 : reg (bv 128)) => do
      v_12215 <- getRegister v_3007;
      v_12218 <- getRegister v_3008;
      v_12222 <- evaluateAddress v_3009;
      v_12223 <- load v_12222 16;
      setRegister (lhs.of_reg v_3008) (concat (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_12215 0 32) 24 8) (MInt2Float (extract v_12218 0 32) 24 8)) (MInt2Float (extract v_12223 0 32) 24 8)) 32) (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_12215 32 64) 24 8) (MInt2Float (extract v_12218 32 64) 24 8)) (MInt2Float (extract v_12223 32 64) 24 8)) 32)) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_12215 64 96) 24 8) (MInt2Float (extract v_12218 64 96) 24 8)) (MInt2Float (extract v_12223 64 96) 24 8)) 32) (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_12215 96 128) 24 8) (MInt2Float (extract v_12218 96 128) 24 8)) (MInt2Float (extract v_12223 96 128) 24 8)) 32)));
      pure ()
    pat_end;
    pattern fun (v_3018 : Mem) (v_3019 : reg (bv 256)) (v_3020 : reg (bv 256)) => do
      v_12259 <- getRegister v_3019;
      v_12262 <- getRegister v_3020;
      v_12266 <- evaluateAddress v_3018;
      v_12267 <- load v_12266 32;
      setRegister (lhs.of_reg v_3020) (concat (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_12259 0 32) 24 8) (MInt2Float (extract v_12262 0 32) 24 8)) (MInt2Float (extract v_12267 0 32) 24 8)) 32) (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_12259 32 64) 24 8) (MInt2Float (extract v_12262 32 64) 24 8)) (MInt2Float (extract v_12267 32 64) 24 8)) 32)) (concat (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_12259 64 96) 24 8) (MInt2Float (extract v_12262 64 96) 24 8)) (MInt2Float (extract v_12267 64 96) 24 8)) 32) (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_12259 96 128) 24 8) (MInt2Float (extract v_12262 96 128) 24 8)) (MInt2Float (extract v_12267 96 128) 24 8)) 32)) (concat (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_12259 128 160) 24 8) (MInt2Float (extract v_12262 128 160) 24 8)) (MInt2Float (extract v_12267 128 160) 24 8)) 32) (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_12259 160 192) 24 8) (MInt2Float (extract v_12262 160 192) 24 8)) (MInt2Float (extract v_12267 160 192) 24 8)) 32)) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_12259 192 224) 24 8) (MInt2Float (extract v_12262 192 224) 24 8)) (MInt2Float (extract v_12267 192 224) 24 8)) 32) (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_12259 224 256) 24 8) (MInt2Float (extract v_12262 224 256) 24 8)) (MInt2Float (extract v_12267 224 256) 24 8)) 32)))));
      pure ()
    pat_end
