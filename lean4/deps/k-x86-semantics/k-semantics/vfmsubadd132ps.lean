def vfmsubadd132ps1 : instruction :=
  definst "vfmsubadd132ps" $ do
    pattern fun (v_3057 : reg (bv 128)) (v_3058 : reg (bv 128)) (v_3059 : reg (bv 128)) => do
      v_6308 <- getRegister v_3059;
      v_6311 <- getRegister v_3057;
      v_6315 <- getRegister v_3058;
      setRegister (lhs.of_reg v_3059) (concat (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_6308 0 32) 24 8) (MInt2Float (extract v_6311 0 32) 24 8)) (MInt2Float (extract v_6315 0 32) 24 8)) 32) (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_6308 32 64) 24 8) (MInt2Float (extract v_6311 32 64) 24 8)) (MInt2Float (extract v_6315 32 64) 24 8)) 32)) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_6308 64 96) 24 8) (MInt2Float (extract v_6311 64 96) 24 8)) (MInt2Float (extract v_6315 64 96) 24 8)) 32) (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_6308 96 128) 24 8) (MInt2Float (extract v_6311 96 128) 24 8)) (MInt2Float (extract v_6315 96 128) 24 8)) 32)));
      pure ()
    pat_end;
    pattern fun (v_3071 : reg (bv 256)) (v_3072 : reg (bv 256)) (v_3073 : reg (bv 256)) => do
      v_6356 <- getRegister v_3073;
      v_6359 <- getRegister v_3071;
      v_6363 <- getRegister v_3072;
      setRegister (lhs.of_reg v_3073) (concat (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_6356 0 32) 24 8) (MInt2Float (extract v_6359 0 32) 24 8)) (MInt2Float (extract v_6363 0 32) 24 8)) 32) (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_6356 32 64) 24 8) (MInt2Float (extract v_6359 32 64) 24 8)) (MInt2Float (extract v_6363 32 64) 24 8)) 32)) (concat (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_6356 64 96) 24 8) (MInt2Float (extract v_6359 64 96) 24 8)) (MInt2Float (extract v_6363 64 96) 24 8)) 32) (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_6356 96 128) 24 8) (MInt2Float (extract v_6359 96 128) 24 8)) (MInt2Float (extract v_6363 96 128) 24 8)) 32)) (concat (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_6356 128 160) 24 8) (MInt2Float (extract v_6359 128 160) 24 8)) (MInt2Float (extract v_6363 128 160) 24 8)) 32) (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_6356 160 192) 24 8) (MInt2Float (extract v_6359 160 192) 24 8)) (MInt2Float (extract v_6363 160 192) 24 8)) 32)) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_6356 192 224) 24 8) (MInt2Float (extract v_6359 192 224) 24 8)) (MInt2Float (extract v_6363 192 224) 24 8)) 32) (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_6356 224 256) 24 8) (MInt2Float (extract v_6359 224 256) 24 8)) (MInt2Float (extract v_6363 224 256) 24 8)) 32)))));
      pure ()
    pat_end;
    pattern fun (v_3054 : Mem) (v_3052 : reg (bv 128)) (v_3053 : reg (bv 128)) => do
      v_12130 <- getRegister v_3053;
      v_12133 <- evaluateAddress v_3054;
      v_12134 <- load v_12133 16;
      v_12138 <- getRegister v_3052;
      setRegister (lhs.of_reg v_3053) (concat (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_12130 0 32) 24 8) (MInt2Float (extract v_12134 0 32) 24 8)) (MInt2Float (extract v_12138 0 32) 24 8)) 32) (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_12130 32 64) 24 8) (MInt2Float (extract v_12134 32 64) 24 8)) (MInt2Float (extract v_12138 32 64) 24 8)) 32)) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_12130 64 96) 24 8) (MInt2Float (extract v_12134 64 96) 24 8)) (MInt2Float (extract v_12138 64 96) 24 8)) 32) (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_12130 96 128) 24 8) (MInt2Float (extract v_12134 96 128) 24 8)) (MInt2Float (extract v_12138 96 128) 24 8)) 32)));
      pure ()
    pat_end;
    pattern fun (v_3063 : Mem) (v_3066 : reg (bv 256)) (v_3067 : reg (bv 256)) => do
      v_12174 <- getRegister v_3067;
      v_12177 <- evaluateAddress v_3063;
      v_12178 <- load v_12177 32;
      v_12182 <- getRegister v_3066;
      setRegister (lhs.of_reg v_3067) (concat (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_12174 0 32) 24 8) (MInt2Float (extract v_12178 0 32) 24 8)) (MInt2Float (extract v_12182 0 32) 24 8)) 32) (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_12174 32 64) 24 8) (MInt2Float (extract v_12178 32 64) 24 8)) (MInt2Float (extract v_12182 32 64) 24 8)) 32)) (concat (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_12174 64 96) 24 8) (MInt2Float (extract v_12178 64 96) 24 8)) (MInt2Float (extract v_12182 64 96) 24 8)) 32) (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_12174 96 128) 24 8) (MInt2Float (extract v_12178 96 128) 24 8)) (MInt2Float (extract v_12182 96 128) 24 8)) 32)) (concat (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_12174 128 160) 24 8) (MInt2Float (extract v_12178 128 160) 24 8)) (MInt2Float (extract v_12182 128 160) 24 8)) 32) (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_12174 160 192) 24 8) (MInt2Float (extract v_12178 160 192) 24 8)) (MInt2Float (extract v_12182 160 192) 24 8)) 32)) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_12174 192 224) 24 8) (MInt2Float (extract v_12178 192 224) 24 8)) (MInt2Float (extract v_12182 192 224) 24 8)) 32) (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_12174 224 256) 24 8) (MInt2Float (extract v_12178 224 256) 24 8)) (MInt2Float (extract v_12182 224 256) 24 8)) 32)))));
      pure ()
    pat_end
