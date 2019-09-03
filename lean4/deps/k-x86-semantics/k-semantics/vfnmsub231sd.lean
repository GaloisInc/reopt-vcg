def vfnmsub231sd1 : instruction :=
  definst "vfnmsub231sd" $ do
    pattern fun (v_3452 : reg (bv 128)) (v_3453 : reg (bv 128)) (v_3454 : reg (bv 128)) => do
      v_8015 <- getRegister v_3454;
      v_8017 <- getRegister v_3453;
      v_8018 <- eval (extract v_8017 32 64);
      v_8020 <- eval (extract v_8017 96 128);
      v_8034 <- getRegister v_3452;
      setRegister (lhs.of_reg v_3454) (concat (extract v_8015 0 64) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (concat (expression.bv_nat 32 0) (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX mincmp_double (concat (expression.bv_nat 32 0) v_8018) (concat (expression.bv_nat 32 0) v_8020)) (expression.bv_nat 1 1)) v_8018 v_8020)) 53 11) (MInt2Float (concat (expression.bv_nat 32 0) (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX mincmp_double (concat (expression.bv_nat 32 0) v_8018) (concat (expression.bv_nat 32 0) v_8020)) (expression.bv_nat 1 1)) v_8018 v_8020)) 53 11))) (MInt2Float (extract v_8017 64 128) 53 11)) 64) 53 11) (MInt2Float (extract v_8034 64 128) 53 11)) (MInt2Float (extract v_8015 64 128) 53 11)) 64));
      pure ()
    pat_end;
    pattern fun (v_3449 : Mem) (v_3447 : reg (bv 128)) (v_3448 : reg (bv 128)) => do
      v_13634 <- getRegister v_3448;
      v_13636 <- getRegister v_3447;
      v_13637 <- eval (extract v_13636 32 64);
      v_13639 <- eval (extract v_13636 96 128);
      v_13653 <- evaluateAddress v_3449;
      v_13654 <- load v_13653 8;
      setRegister (lhs.of_reg v_3448) (concat (extract v_13634 0 64) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (concat (expression.bv_nat 32 0) (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX mincmp_double (concat (expression.bv_nat 32 0) v_13637) (concat (expression.bv_nat 32 0) v_13639)) (expression.bv_nat 1 1)) v_13637 v_13639)) 53 11) (MInt2Float (concat (expression.bv_nat 32 0) (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX mincmp_double (concat (expression.bv_nat 32 0) v_13637) (concat (expression.bv_nat 32 0) v_13639)) (expression.bv_nat 1 1)) v_13637 v_13639)) 53 11))) (MInt2Float (extract v_13636 64 128) 53 11)) 64) 53 11) (MInt2Float v_13654 53 11)) (MInt2Float (extract v_13634 64 128) 53 11)) 64));
      pure ()
    pat_end
