def vfmadd213ps1 : instruction :=
  definst "vfmadd213ps" $ do
    pattern fun (mem_0 : Mem) (xmm_1 : reg (bv 128)) (xmm_2 : reg (bv 128)) => do
      v_3 <- getRegister xmm_1;
      v_4 <- getRegister xmm_2;
      v_5 <- evaluateAddress mem_0;
      v_6 <- load v_5 16;
      v_7 <- eval (MInt2Float (extract v_6 0 32) 24 8);
      v_8 <- eval (MInt2Float (extract v_6 32 64) 24 8);
      v_9 <- eval (MInt2Float (extract v_6 64 96) 24 8);
      v_10 <- eval (MInt2Float (extract v_6 96 128) 24 8);
      setRegister (lhs.of_reg xmm_2) (concat (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_3 0 32) 24 8) (MInt2Float (extract v_4 0 32) 24 8)) (MInt2Float (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (expression.bv_nat 32 0) 24 8) v_7)) v_7) 32) 24 8)) 32) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_3 32 64) 24 8) (MInt2Float (extract v_4 32 64) 24 8)) (MInt2Float (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (expression.bv_nat 32 0) 24 8) v_8)) v_8) 32) 24 8)) 32)) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_3 64 96) 24 8) (MInt2Float (extract v_4 64 96) 24 8)) (MInt2Float (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (expression.bv_nat 32 0) 24 8) v_9)) v_9) 32) 24 8)) 32) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_3 96 128) 24 8) (MInt2Float (extract v_4 96 128) 24 8)) (MInt2Float (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (expression.bv_nat 32 0) 24 8) v_10)) v_10) 32) 24 8)) 32)));
      pure ()
    pat_end;
    pattern fun (mem_0 : Mem) (ymm_1 : reg (bv 256)) (ymm_2 : reg (bv 256)) => do
      v_3 <- getRegister ymm_1;
      v_4 <- getRegister ymm_2;
      v_5 <- evaluateAddress mem_0;
      v_6 <- load v_5 32;
      setRegister (lhs.of_reg ymm_2) (concat (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_3 0 32) 24 8) (MInt2Float (extract v_4 0 32) 24 8)) (MInt2Float (extract v_6 0 32) 24 8)) 32) (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_3 32 64) 24 8) (MInt2Float (extract v_4 32 64) 24 8)) (MInt2Float (extract v_6 32 64) 24 8)) 32)) (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_3 64 96) 24 8) (MInt2Float (extract v_4 64 96) 24 8)) (MInt2Float (extract v_6 64 96) 24 8)) 32) (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_3 96 128) 24 8) (MInt2Float (extract v_4 96 128) 24 8)) (MInt2Float (extract v_6 96 128) 24 8)) 32) (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_3 128 160) 24 8) (MInt2Float (extract v_4 128 160) 24 8)) (MInt2Float (extract v_6 128 160) 24 8)) 32) (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_3 160 192) 24 8) (MInt2Float (extract v_4 160 192) 24 8)) (MInt2Float (extract v_6 160 192) 24 8)) 32) (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_3 192 224) 24 8) (MInt2Float (extract v_4 192 224) 24 8)) (MInt2Float (extract v_6 192 224) 24 8)) 32) (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_3 224 256) 24 8) (MInt2Float (extract v_4 224 256) 24 8)) (MInt2Float (extract v_6 224 256) 24 8)) 32)))))));
      pure ()
    pat_end;
    pattern fun (xmm_0 : reg (bv 128)) (xmm_1 : reg (bv 128)) (xmm_2 : reg (bv 128)) => do
      v_3 <- getRegister xmm_1;
      v_4 <- getRegister xmm_2;
      v_5 <- getRegister xmm_0;
      v_6 <- eval (MInt2Float (extract v_5 0 32) 24 8);
      v_7 <- eval (MInt2Float (extract v_5 32 64) 24 8);
      v_8 <- eval (MInt2Float (extract v_5 64 96) 24 8);
      v_9 <- eval (MInt2Float (extract v_5 96 128) 24 8);
      setRegister (lhs.of_reg xmm_2) (concat (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_3 0 32) 24 8) (MInt2Float (extract v_4 0 32) 24 8)) (MInt2Float (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (expression.bv_nat 32 0) 24 8) v_6)) v_6) 32) 24 8)) 32) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_3 32 64) 24 8) (MInt2Float (extract v_4 32 64) 24 8)) (MInt2Float (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (expression.bv_nat 32 0) 24 8) v_7)) v_7) 32) 24 8)) 32)) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_3 64 96) 24 8) (MInt2Float (extract v_4 64 96) 24 8)) (MInt2Float (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (expression.bv_nat 32 0) 24 8) v_8)) v_8) 32) 24 8)) 32) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_3 96 128) 24 8) (MInt2Float (extract v_4 96 128) 24 8)) (MInt2Float (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (expression.bv_nat 32 0) 24 8) v_9)) v_9) 32) 24 8)) 32)));
      pure ()
    pat_end;
    pattern fun (ymm_0 : reg (bv 256)) (ymm_1 : reg (bv 256)) (ymm_2 : reg (bv 256)) => do
      v_3 <- getRegister ymm_1;
      v_4 <- getRegister ymm_2;
      v_5 <- getRegister ymm_0;
      setRegister (lhs.of_reg ymm_2) (concat (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_3 0 32) 24 8) (MInt2Float (extract v_4 0 32) 24 8)) (MInt2Float (extract v_5 0 32) 24 8)) 32) (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_3 32 64) 24 8) (MInt2Float (extract v_4 32 64) 24 8)) (MInt2Float (extract v_5 32 64) 24 8)) 32)) (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_3 64 96) 24 8) (MInt2Float (extract v_4 64 96) 24 8)) (MInt2Float (extract v_5 64 96) 24 8)) 32) (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_3 96 128) 24 8) (MInt2Float (extract v_4 96 128) 24 8)) (MInt2Float (extract v_5 96 128) 24 8)) 32) (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_3 128 160) 24 8) (MInt2Float (extract v_4 128 160) 24 8)) (MInt2Float (extract v_5 128 160) 24 8)) 32) (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_3 160 192) 24 8) (MInt2Float (extract v_4 160 192) 24 8)) (MInt2Float (extract v_5 160 192) 24 8)) 32) (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_3 192 224) 24 8) (MInt2Float (extract v_4 192 224) 24 8)) (MInt2Float (extract v_5 192 224) 24 8)) 32) (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_3 224 256) 24 8) (MInt2Float (extract v_4 224 256) 24 8)) (MInt2Float (extract v_5 224 256) 24 8)) 32)))))));
      pure ()
    pat_end
