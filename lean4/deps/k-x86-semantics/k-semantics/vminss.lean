def vminss1 : instruction :=
  definst "vminss" $ do
    pattern fun (v_2723 : reg (bv 128)) (v_2724 : reg (bv 128)) (v_2725 : reg (bv 128)) => do
      v_4693 <- getRegister v_2724;
      v_4695 <- eval (extract v_4693 96 128);
      v_4696 <- getRegister v_2723;
      v_4697 <- eval (extract v_4696 96 128);
      setRegister (lhs.of_reg v_2725) (concat (extract v_4693 0 96) (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX mincmp_single v_4695 v_4697) (expression.bv_nat 1 1)) v_4695 v_4697));
      pure ()
    pat_end;
    pattern fun (v_2718 : Mem) (v_2719 : reg (bv 128)) (v_2720 : reg (bv 128)) => do
      v_10114 <- getRegister v_2719;
      v_10116 <- eval (extract v_10114 96 128);
      v_10117 <- evaluateAddress v_2718;
      v_10118 <- load v_10117 4;
      setRegister (lhs.of_reg v_2720) (concat (extract v_10114 0 96) (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX mincmp_single v_10116 v_10118) (expression.bv_nat 1 1)) v_10116 v_10118));
      pure ()
    pat_end
