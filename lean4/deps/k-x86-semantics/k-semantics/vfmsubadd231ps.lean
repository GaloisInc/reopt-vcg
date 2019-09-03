def vfmsubadd231ps1 : instruction :=
  definst "vfmsubadd231ps" $ do
    pattern fun (v_3056 : reg (bv 128)) (v_3057 : reg (bv 128)) (v_3058 : reg (bv 128)) => do
      v_6638 <- getRegister v_3057;
      v_6641 <- getRegister v_3056;
      v_6645 <- getRegister v_3058;
      setRegister (lhs.of_reg v_3058) (concat (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_6638 0 32) 24 8) (MInt2Float (extract v_6641 0 32) 24 8)) (MInt2Float (extract v_6645 0 32) 24 8)) 32) (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_6638 32 64) 24 8) (MInt2Float (extract v_6641 32 64) 24 8)) (MInt2Float (extract v_6645 32 64) 24 8)) 32)) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_6638 64 96) 24 8) (MInt2Float (extract v_6641 64 96) 24 8)) (MInt2Float (extract v_6645 64 96) 24 8)) 32) (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_6638 96 128) 24 8) (MInt2Float (extract v_6641 96 128) 24 8)) (MInt2Float (extract v_6645 96 128) 24 8)) 32)));
      pure ()
    pat_end;
    pattern fun (v_3068 : reg (bv 256)) (v_3069 : reg (bv 256)) (v_3070 : reg (bv 256)) => do
      v_6686 <- getRegister v_3069;
      v_6689 <- getRegister v_3068;
      v_6693 <- getRegister v_3070;
      setRegister (lhs.of_reg v_3070) (concat (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_6686 0 32) 24 8) (MInt2Float (extract v_6689 0 32) 24 8)) (MInt2Float (extract v_6693 0 32) 24 8)) 32) (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_6686 32 64) 24 8) (MInt2Float (extract v_6689 32 64) 24 8)) (MInt2Float (extract v_6693 32 64) 24 8)) 32)) (concat (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_6686 64 96) 24 8) (MInt2Float (extract v_6689 64 96) 24 8)) (MInt2Float (extract v_6693 64 96) 24 8)) 32) (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_6686 96 128) 24 8) (MInt2Float (extract v_6689 96 128) 24 8)) (MInt2Float (extract v_6693 96 128) 24 8)) 32)) (concat (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_6686 128 160) 24 8) (MInt2Float (extract v_6689 128 160) 24 8)) (MInt2Float (extract v_6693 128 160) 24 8)) 32) (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_6686 160 192) 24 8) (MInt2Float (extract v_6689 160 192) 24 8)) (MInt2Float (extract v_6693 160 192) 24 8)) 32)) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_6686 192 224) 24 8) (MInt2Float (extract v_6689 192 224) 24 8)) (MInt2Float (extract v_6693 192 224) 24 8)) 32) (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_6686 224 256) 24 8) (MInt2Float (extract v_6689 224 256) 24 8)) (MInt2Float (extract v_6693 224 256) 24 8)) 32)))));
      pure ()
    pat_end;
    pattern fun (v_3053 : Mem) (v_3051 : reg (bv 128)) (v_3052 : reg (bv 128)) => do
      v_12411 <- getRegister v_3051;
      v_12414 <- evaluateAddress v_3053;
      v_12415 <- load v_12414 16;
      v_12419 <- getRegister v_3052;
      setRegister (lhs.of_reg v_3052) (concat (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_12411 0 32) 24 8) (MInt2Float (extract v_12415 0 32) 24 8)) (MInt2Float (extract v_12419 0 32) 24 8)) 32) (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_12411 32 64) 24 8) (MInt2Float (extract v_12415 32 64) 24 8)) (MInt2Float (extract v_12419 32 64) 24 8)) 32)) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_12411 64 96) 24 8) (MInt2Float (extract v_12415 64 96) 24 8)) (MInt2Float (extract v_12419 64 96) 24 8)) 32) (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_12411 96 128) 24 8) (MInt2Float (extract v_12415 96 128) 24 8)) (MInt2Float (extract v_12419 96 128) 24 8)) 32)));
      pure ()
    pat_end;
    pattern fun (v_3062 : Mem) (v_3063 : reg (bv 256)) (v_3064 : reg (bv 256)) => do
      v_12455 <- getRegister v_3063;
      v_12458 <- evaluateAddress v_3062;
      v_12459 <- load v_12458 32;
      v_12463 <- getRegister v_3064;
      setRegister (lhs.of_reg v_3064) (concat (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_12455 0 32) 24 8) (MInt2Float (extract v_12459 0 32) 24 8)) (MInt2Float (extract v_12463 0 32) 24 8)) 32) (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_12455 32 64) 24 8) (MInt2Float (extract v_12459 32 64) 24 8)) (MInt2Float (extract v_12463 32 64) 24 8)) 32)) (concat (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_12455 64 96) 24 8) (MInt2Float (extract v_12459 64 96) 24 8)) (MInt2Float (extract v_12463 64 96) 24 8)) 32) (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_12455 96 128) 24 8) (MInt2Float (extract v_12459 96 128) 24 8)) (MInt2Float (extract v_12463 96 128) 24 8)) 32)) (concat (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_12455 128 160) 24 8) (MInt2Float (extract v_12459 128 160) 24 8)) (MInt2Float (extract v_12463 128 160) 24 8)) 32) (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_12455 160 192) 24 8) (MInt2Float (extract v_12459 160 192) 24 8)) (MInt2Float (extract v_12463 160 192) 24 8)) 32)) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_12455 192 224) 24 8) (MInt2Float (extract v_12459 192 224) 24 8)) (MInt2Float (extract v_12463 192 224) 24 8)) 32) (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_12455 224 256) 24 8) (MInt2Float (extract v_12459 224 256) 24 8)) (MInt2Float (extract v_12463 224 256) 24 8)) 32)))));
      pure ()
    pat_end
