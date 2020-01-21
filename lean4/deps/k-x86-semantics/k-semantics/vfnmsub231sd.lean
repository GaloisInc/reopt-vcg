def vfnmsub231sd : instruction :=
  definst "vfnmsub231sd" $ do
    pattern fun (mem_0 : Mem) (xmm_1 : reg (bv 128)) (xmm_2 : reg (bv 128)) => do
      v_3 <- getRegister (lhs.of_reg xmm_2);
      v_4 <- getRegister (lhs.of_reg xmm_1);
      v_5 <- eval (extract v_4 32 64);
      v_6 <- eval (extract v_4 96 128);
      v_7 <- evaluateAddress mem_0;
      v_8 <- load v_7 8;
      setRegister (lhs.of_reg xmm_2) (concat (extract v_3 0 64) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (concat (expression.bv_nat 32 0) (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX mincmp_double (concat (expression.bv_nat 32 0) v_5) (concat (expression.bv_nat 32 0) v_6)) (expression.bv_nat 1 1)) v_5 v_6)) 53 11) (MInt2Float (concat (expression.bv_nat 32 0) (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX mincmp_double (concat (expression.bv_nat 32 0) v_5) (concat (expression.bv_nat 32 0) v_6)) (expression.bv_nat 1 1)) v_5 v_6)) 53 11))) (MInt2Float (extract v_4 64 128) 53 11)) 64) 53 11) (MInt2Float v_8 53 11)) (MInt2Float (extract v_3 64 128) 53 11)) 64));
      pure ()
    pat_end;
    pattern fun (xmm_0 : reg (bv 128)) (xmm_1 : reg (bv 128)) (xmm_2 : reg (bv 128)) => do
      v_3 <- getRegister (lhs.of_reg xmm_2);
      v_4 <- getRegister (lhs.of_reg xmm_1);
      v_5 <- eval (extract v_4 32 64);
      v_6 <- eval (extract v_4 96 128);
      v_7 <- getRegister (lhs.of_reg xmm_0);
      setRegister (lhs.of_reg xmm_2) (concat (extract v_3 0 64) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (concat (expression.bv_nat 32 0) (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX mincmp_double (concat (expression.bv_nat 32 0) v_5) (concat (expression.bv_nat 32 0) v_6)) (expression.bv_nat 1 1)) v_5 v_6)) 53 11) (MInt2Float (concat (expression.bv_nat 32 0) (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX mincmp_double (concat (expression.bv_nat 32 0) v_5) (concat (expression.bv_nat 32 0) v_6)) (expression.bv_nat 1 1)) v_5 v_6)) 53 11))) (MInt2Float (extract v_4 64 128) 53 11)) 64) 53 11) (MInt2Float (extract v_7 64 128) 53 11)) (MInt2Float (extract v_3 64 128) 53 11)) 64));
      pure ()
    pat_end
