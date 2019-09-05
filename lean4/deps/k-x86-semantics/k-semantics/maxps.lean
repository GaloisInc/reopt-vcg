def maxps1 : instruction :=
  definst "maxps" $ do
    pattern fun (v_3125 : reg (bv 128)) (v_3126 : reg (bv 128)) => do
      v_5579 <- getRegister v_3126;
      v_5580 <- eval (extract v_5579 0 32);
      v_5581 <- getRegister v_3125;
      v_5582 <- eval (extract v_5581 0 32);
      v_5586 <- eval (extract v_5579 32 64);
      v_5587 <- eval (extract v_5581 32 64);
      v_5591 <- eval (extract v_5579 64 96);
      v_5592 <- eval (extract v_5581 64 96);
      v_5596 <- eval (extract v_5579 96 128);
      v_5597 <- eval (extract v_5581 96 128);
      setRegister (lhs.of_reg v_3126) (concat (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX maxcmp_single v_5580 v_5582) (expression.bv_nat 1 1)) v_5580 v_5582) (concat (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX maxcmp_single v_5586 v_5587) (expression.bv_nat 1 1)) v_5586 v_5587) (concat (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX maxcmp_single v_5591 v_5592) (expression.bv_nat 1 1)) v_5591 v_5592) (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX maxcmp_single v_5596 v_5597) (expression.bv_nat 1 1)) v_5596 v_5597))));
      pure ()
    pat_end;
    pattern fun (v_3120 : Mem) (v_3121 : reg (bv 128)) => do
      v_8837 <- getRegister v_3121;
      v_8838 <- eval (extract v_8837 0 32);
      v_8839 <- evaluateAddress v_3120;
      v_8840 <- load v_8839 16;
      v_8841 <- eval (extract v_8840 0 32);
      v_8845 <- eval (extract v_8837 32 64);
      v_8846 <- eval (extract v_8840 32 64);
      v_8850 <- eval (extract v_8837 64 96);
      v_8851 <- eval (extract v_8840 64 96);
      v_8855 <- eval (extract v_8837 96 128);
      v_8856 <- eval (extract v_8840 96 128);
      setRegister (lhs.of_reg v_3121) (concat (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX maxcmp_single v_8838 v_8841) (expression.bv_nat 1 1)) v_8838 v_8841) (concat (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX maxcmp_single v_8845 v_8846) (expression.bv_nat 1 1)) v_8845 v_8846) (concat (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX maxcmp_single v_8850 v_8851) (expression.bv_nat 1 1)) v_8850 v_8851) (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX maxcmp_single v_8855 v_8856) (expression.bv_nat 1 1)) v_8855 v_8856))));
      pure ()
    pat_end
