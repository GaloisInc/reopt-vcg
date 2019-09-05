def minsd1 : instruction :=
  definst "minsd" $ do
    pattern fun (v_3170 : reg (bv 128)) (v_3171 : reg (bv 128)) => do
      v_5685 <- getRegister v_3171;
      v_5687 <- eval (extract v_5685 64 128);
      v_5688 <- getRegister v_3170;
      v_5689 <- eval (extract v_5688 64 128);
      setRegister (lhs.of_reg v_3171) (concat (extract v_5685 0 64) (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX mincmp_double v_5687 v_5689) (expression.bv_nat 1 1)) v_5687 v_5689));
      pure ()
    pat_end;
    pattern fun (v_3165 : Mem) (v_3166 : reg (bv 128)) => do
      v_8926 <- getRegister v_3166;
      v_8928 <- eval (extract v_8926 64 128);
      v_8929 <- evaluateAddress v_3165;
      v_8930 <- load v_8929 8;
      setRegister (lhs.of_reg v_3166) (concat (extract v_8926 0 64) (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX mincmp_double v_8928 v_8930) (expression.bv_nat 1 1)) v_8928 v_8930));
      pure ()
    pat_end
