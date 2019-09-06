def minsd1 : instruction :=
  definst "minsd" $ do
    pattern fun (v_3196 : reg (bv 128)) (v_3197 : reg (bv 128)) => do
      v_5701 <- getRegister v_3197;
      v_5703 <- eval (extract v_5701 64 128);
      v_5704 <- getRegister v_3196;
      v_5705 <- eval (extract v_5704 64 128);
      setRegister (lhs.of_reg v_3197) (concat (extract v_5701 0 64) (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX mincmp_double v_5703 v_5705) (expression.bv_nat 1 1)) v_5703 v_5705));
      pure ()
    pat_end;
    pattern fun (v_3192 : Mem) (v_3193 : reg (bv 128)) => do
      v_8936 <- getRegister v_3193;
      v_8938 <- eval (extract v_8936 64 128);
      v_8939 <- evaluateAddress v_3192;
      v_8940 <- load v_8939 8;
      setRegister (lhs.of_reg v_3193) (concat (extract v_8936 0 64) (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX mincmp_double v_8938 v_8940) (expression.bv_nat 1 1)) v_8938 v_8940));
      pure ()
    pat_end
