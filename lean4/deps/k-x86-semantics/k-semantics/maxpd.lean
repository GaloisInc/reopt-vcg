def maxpd1 : instruction :=
  definst "maxpd" $ do
    pattern fun (v_3142 : reg (bv 128)) (v_3143 : reg (bv 128)) => do
      v_5577 <- getRegister v_3143;
      v_5578 <- eval (extract v_5577 0 64);
      v_5579 <- getRegister v_3142;
      v_5580 <- eval (extract v_5579 0 64);
      v_5584 <- eval (extract v_5577 64 128);
      v_5585 <- eval (extract v_5579 64 128);
      setRegister (lhs.of_reg v_3143) (concat (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX maxcmp_double v_5578 v_5580) (expression.bv_nat 1 1)) v_5578 v_5580) (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX maxcmp_double v_5584 v_5585) (expression.bv_nat 1 1)) v_5584 v_5585));
      pure ()
    pat_end;
    pattern fun (v_3138 : Mem) (v_3139 : reg (bv 128)) => do
      v_8832 <- getRegister v_3139;
      v_8833 <- eval (extract v_8832 0 64);
      v_8834 <- evaluateAddress v_3138;
      v_8835 <- load v_8834 16;
      v_8836 <- eval (extract v_8835 0 64);
      v_8840 <- eval (extract v_8832 64 128);
      v_8841 <- eval (extract v_8835 64 128);
      setRegister (lhs.of_reg v_3139) (concat (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX maxcmp_double v_8833 v_8836) (expression.bv_nat 1 1)) v_8833 v_8836) (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX maxcmp_double v_8840 v_8841) (expression.bv_nat 1 1)) v_8840 v_8841));
      pure ()
    pat_end
