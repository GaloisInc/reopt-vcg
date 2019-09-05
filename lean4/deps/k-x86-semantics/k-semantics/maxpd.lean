def maxpd1 : instruction :=
  definst "maxpd" $ do
    pattern fun (v_3116 : reg (bv 128)) (v_3117 : reg (bv 128)) => do
      v_5561 <- getRegister v_3117;
      v_5562 <- eval (extract v_5561 0 64);
      v_5563 <- getRegister v_3116;
      v_5564 <- eval (extract v_5563 0 64);
      v_5568 <- eval (extract v_5561 64 128);
      v_5569 <- eval (extract v_5563 64 128);
      setRegister (lhs.of_reg v_3117) (concat (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX maxcmp_double v_5562 v_5564) (expression.bv_nat 1 1)) v_5562 v_5564) (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX maxcmp_double v_5568 v_5569) (expression.bv_nat 1 1)) v_5568 v_5569));
      pure ()
    pat_end;
    pattern fun (v_3111 : Mem) (v_3112 : reg (bv 128)) => do
      v_8822 <- getRegister v_3112;
      v_8823 <- eval (extract v_8822 0 64);
      v_8824 <- evaluateAddress v_3111;
      v_8825 <- load v_8824 16;
      v_8826 <- eval (extract v_8825 0 64);
      v_8830 <- eval (extract v_8822 64 128);
      v_8831 <- eval (extract v_8825 64 128);
      setRegister (lhs.of_reg v_3112) (concat (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX maxcmp_double v_8823 v_8826) (expression.bv_nat 1 1)) v_8823 v_8826) (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX maxcmp_double v_8830 v_8831) (expression.bv_nat 1 1)) v_8830 v_8831));
      pure ()
    pat_end
