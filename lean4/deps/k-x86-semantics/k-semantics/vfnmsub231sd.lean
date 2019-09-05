def vfnmsub231sd1 : instruction :=
  definst "vfnmsub231sd" $ do
    pattern fun (v_3517 : reg (bv 128)) (v_3518 : reg (bv 128)) (v_3519 : reg (bv 128)) => do
      v_8092 <- getRegister v_3519;
      v_8094 <- getRegister v_3518;
      v_8095 <- eval (extract v_8094 32 64);
      v_8097 <- eval (extract v_8094 96 128);
      v_8111 <- getRegister v_3517;
      setRegister (lhs.of_reg v_3519) (concat (extract v_8092 0 64) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (concat (expression.bv_nat 32 0) (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX mincmp_double (concat (expression.bv_nat 32 0) v_8095) (concat (expression.bv_nat 32 0) v_8097)) (expression.bv_nat 1 1)) v_8095 v_8097)) 53 11) (MInt2Float (concat (expression.bv_nat 32 0) (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX mincmp_double (concat (expression.bv_nat 32 0) v_8095) (concat (expression.bv_nat 32 0) v_8097)) (expression.bv_nat 1 1)) v_8095 v_8097)) 53 11))) (MInt2Float (extract v_8094 64 128) 53 11)) 64) 53 11) (MInt2Float (extract v_8111 64 128) 53 11)) (MInt2Float (extract v_8092 64 128) 53 11)) 64));
      pure ()
    pat_end;
    pattern fun (v_3511 : Mem) (v_3512 : reg (bv 128)) (v_3513 : reg (bv 128)) => do
      v_13728 <- getRegister v_3513;
      v_13730 <- getRegister v_3512;
      v_13731 <- eval (extract v_13730 32 64);
      v_13733 <- eval (extract v_13730 96 128);
      v_13747 <- evaluateAddress v_3511;
      v_13748 <- load v_13747 8;
      setRegister (lhs.of_reg v_3513) (concat (extract v_13728 0 64) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (concat (expression.bv_nat 32 0) (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX mincmp_double (concat (expression.bv_nat 32 0) v_13731) (concat (expression.bv_nat 32 0) v_13733)) (expression.bv_nat 1 1)) v_13731 v_13733)) 53 11) (MInt2Float (concat (expression.bv_nat 32 0) (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX mincmp_double (concat (expression.bv_nat 32 0) v_13731) (concat (expression.bv_nat 32 0) v_13733)) (expression.bv_nat 1 1)) v_13731 v_13733)) 53 11))) (MInt2Float (extract v_13730 64 128) 53 11)) 64) 53 11) (MInt2Float v_13748 53 11)) (MInt2Float (extract v_13728 64 128) 53 11)) 64));
      pure ()
    pat_end
