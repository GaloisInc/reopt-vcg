def maxsd1 : instruction :=
  definst "maxsd" $ do
    pattern fun (v_3134 : reg (bv 128)) (v_3135 : reg (bv 128)) => do
      v_5609 <- getRegister v_3135;
      v_5611 <- eval (extract v_5609 64 128);
      v_5612 <- getRegister v_3134;
      v_5613 <- eval (extract v_5612 64 128);
      setRegister (lhs.of_reg v_3135) (concat (extract v_5609 0 64) (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX maxcmp_double v_5611 v_5613) (expression.bv_nat 1 1)) v_5611 v_5613));
      pure ()
    pat_end;
    pattern fun (v_3129 : Mem) (v_3130 : reg (bv 128)) => do
      v_8864 <- getRegister v_3130;
      v_8866 <- eval (extract v_8864 64 128);
      v_8867 <- evaluateAddress v_3129;
      v_8868 <- load v_8867 8;
      setRegister (lhs.of_reg v_3130) (concat (extract v_8864 0 64) (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX maxcmp_double v_8866 v_8868) (expression.bv_nat 1 1)) v_8866 v_8868));
      pure ()
    pat_end
