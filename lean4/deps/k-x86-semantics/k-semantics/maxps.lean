def maxps1 : instruction :=
  definst "maxps" $ do
    pattern fun (v_3151 : reg (bv 128)) (v_3152 : reg (bv 128)) => do
      v_5595 <- getRegister v_3152;
      v_5596 <- eval (extract v_5595 0 32);
      v_5597 <- getRegister v_3151;
      v_5598 <- eval (extract v_5597 0 32);
      v_5602 <- eval (extract v_5595 32 64);
      v_5603 <- eval (extract v_5597 32 64);
      v_5607 <- eval (extract v_5595 64 96);
      v_5608 <- eval (extract v_5597 64 96);
      v_5612 <- eval (extract v_5595 96 128);
      v_5613 <- eval (extract v_5597 96 128);
      setRegister (lhs.of_reg v_3152) (concat (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX maxcmp_single v_5596 v_5598) (expression.bv_nat 1 1)) v_5596 v_5598) (concat (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX maxcmp_single v_5602 v_5603) (expression.bv_nat 1 1)) v_5602 v_5603) (concat (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX maxcmp_single v_5607 v_5608) (expression.bv_nat 1 1)) v_5607 v_5608) (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX maxcmp_single v_5612 v_5613) (expression.bv_nat 1 1)) v_5612 v_5613))));
      pure ()
    pat_end;
    pattern fun (v_3147 : Mem) (v_3148 : reg (bv 128)) => do
      v_8847 <- getRegister v_3148;
      v_8848 <- eval (extract v_8847 0 32);
      v_8849 <- evaluateAddress v_3147;
      v_8850 <- load v_8849 16;
      v_8851 <- eval (extract v_8850 0 32);
      v_8855 <- eval (extract v_8847 32 64);
      v_8856 <- eval (extract v_8850 32 64);
      v_8860 <- eval (extract v_8847 64 96);
      v_8861 <- eval (extract v_8850 64 96);
      v_8865 <- eval (extract v_8847 96 128);
      v_8866 <- eval (extract v_8850 96 128);
      setRegister (lhs.of_reg v_3148) (concat (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX maxcmp_single v_8848 v_8851) (expression.bv_nat 1 1)) v_8848 v_8851) (concat (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX maxcmp_single v_8855 v_8856) (expression.bv_nat 1 1)) v_8855 v_8856) (concat (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX maxcmp_single v_8860 v_8861) (expression.bv_nat 1 1)) v_8860 v_8861) (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX maxcmp_single v_8865 v_8866) (expression.bv_nat 1 1)) v_8865 v_8866))));
      pure ()
    pat_end
