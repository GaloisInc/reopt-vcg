def vfnmsub231sd1 : instruction :=
  definst "vfnmsub231sd" $ do
    pattern fun (v_3541 : reg (bv 128)) (v_3542 : reg (bv 128)) (v_3543 : reg (bv 128)) => do
      v_8119 <- getRegister v_3543;
      v_8121 <- getRegister v_3542;
      v_8122 <- eval (extract v_8121 32 64);
      v_8124 <- eval (extract v_8121 96 128);
      v_8138 <- getRegister v_3541;
      setRegister (lhs.of_reg v_3543) (concat (extract v_8119 0 64) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (concat (expression.bv_nat 32 0) (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX mincmp_double (concat (expression.bv_nat 32 0) v_8122) (concat (expression.bv_nat 32 0) v_8124)) (expression.bv_nat 1 1)) v_8122 v_8124)) 53 11) (MInt2Float (concat (expression.bv_nat 32 0) (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX mincmp_double (concat (expression.bv_nat 32 0) v_8122) (concat (expression.bv_nat 32 0) v_8124)) (expression.bv_nat 1 1)) v_8122 v_8124)) 53 11))) (MInt2Float (extract v_8121 64 128) 53 11)) 64) 53 11) (MInt2Float (extract v_8138 64 128) 53 11)) (MInt2Float (extract v_8119 64 128) 53 11)) 64));
      pure ()
    pat_end;
    pattern fun (v_3538 : Mem) (v_3536 : reg (bv 128)) (v_3537 : reg (bv 128)) => do
      v_13755 <- getRegister v_3537;
      v_13757 <- getRegister v_3536;
      v_13758 <- eval (extract v_13757 32 64);
      v_13760 <- eval (extract v_13757 96 128);
      v_13774 <- evaluateAddress v_3538;
      v_13775 <- load v_13774 8;
      setRegister (lhs.of_reg v_3537) (concat (extract v_13755 0 64) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (concat (expression.bv_nat 32 0) (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX mincmp_double (concat (expression.bv_nat 32 0) v_13758) (concat (expression.bv_nat 32 0) v_13760)) (expression.bv_nat 1 1)) v_13758 v_13760)) 53 11) (MInt2Float (concat (expression.bv_nat 32 0) (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX mincmp_double (concat (expression.bv_nat 32 0) v_13758) (concat (expression.bv_nat 32 0) v_13760)) (expression.bv_nat 1 1)) v_13758 v_13760)) 53 11))) (MInt2Float (extract v_13757 64 128) 53 11)) 64) 53 11) (MInt2Float v_13775 53 11)) (MInt2Float (extract v_13755 64 128) 53 11)) 64));
      pure ()
    pat_end
