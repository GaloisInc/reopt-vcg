def vminss1 : instruction :=
  definst "vminss" $ do
    pattern fun (v_2748 : reg (bv 128)) (v_2749 : reg (bv 128)) (v_2750 : reg (bv 128)) => do
      v_4720 <- getRegister v_2749;
      v_4722 <- eval (extract v_4720 96 128);
      v_4723 <- getRegister v_2748;
      v_4724 <- eval (extract v_4723 96 128);
      setRegister (lhs.of_reg v_2750) (concat (extract v_4720 0 96) (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX mincmp_single v_4722 v_4724) (expression.bv_nat 1 1)) v_4722 v_4724));
      pure ()
    pat_end;
    pattern fun (v_2743 : Mem) (v_2744 : reg (bv 128)) (v_2745 : reg (bv 128)) => do
      v_10141 <- getRegister v_2744;
      v_10143 <- eval (extract v_10141 96 128);
      v_10144 <- evaluateAddress v_2743;
      v_10145 <- load v_10144 4;
      setRegister (lhs.of_reg v_2745) (concat (extract v_10141 0 96) (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX mincmp_single v_10143 v_10145) (expression.bv_nat 1 1)) v_10143 v_10145));
      pure ()
    pat_end
