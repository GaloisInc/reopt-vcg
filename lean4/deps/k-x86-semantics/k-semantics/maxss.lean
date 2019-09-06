def maxss1 : instruction :=
  definst "maxss" $ do
    pattern fun (v_3169 : reg (bv 128)) (v_3170 : reg (bv 128)) => do
      v_5639 <- getRegister v_3170;
      v_5641 <- eval (extract v_5639 96 128);
      v_5642 <- getRegister v_3169;
      v_5643 <- eval (extract v_5642 96 128);
      setRegister (lhs.of_reg v_3170) (concat (extract v_5639 0 96) (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX maxcmp_single v_5641 v_5643) (expression.bv_nat 1 1)) v_5641 v_5643));
      pure ()
    pat_end;
    pattern fun (v_3165 : Mem) (v_3166 : reg (bv 128)) => do
      v_8884 <- getRegister v_3166;
      v_8886 <- eval (extract v_8884 96 128);
      v_8887 <- evaluateAddress v_3165;
      v_8888 <- load v_8887 4;
      setRegister (lhs.of_reg v_3166) (concat (extract v_8884 0 96) (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX maxcmp_single v_8886 v_8888) (expression.bv_nat 1 1)) v_8886 v_8888));
      pure ()
    pat_end
