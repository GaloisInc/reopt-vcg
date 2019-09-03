def vmaxsd1 : instruction :=
  definst "vmaxsd" $ do
    pattern fun (v_2595 : reg (bv 128)) (v_2596 : reg (bv 128)) (v_2597 : reg (bv 128)) => do
      v_4827 <- getRegister v_2596;
      v_4829 <- eval (extract v_4827 64 128);
      v_4830 <- getRegister v_2595;
      v_4831 <- eval (extract v_4830 64 128);
      setRegister (lhs.of_reg v_2597) (concat (extract v_4827 0 64) (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX maxcmp_double v_4829 v_4831) (expression.bv_nat 1 1)) v_4829 v_4831));
      pure ()
    pat_end;
    pattern fun (v_2590 : Mem) (v_2591 : reg (bv 128)) (v_2592 : reg (bv 128)) => do
      v_10903 <- getRegister v_2591;
      v_10905 <- eval (extract v_10903 64 128);
      v_10906 <- evaluateAddress v_2590;
      v_10907 <- load v_10906 8;
      setRegister (lhs.of_reg v_2592) (concat (extract v_10903 0 64) (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX maxcmp_double v_10905 v_10907) (expression.bv_nat 1 1)) v_10905 v_10907));
      pure ()
    pat_end
