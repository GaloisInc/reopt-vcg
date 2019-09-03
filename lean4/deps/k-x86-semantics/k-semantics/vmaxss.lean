def vmaxss1 : instruction :=
  definst "vmaxss" $ do
    pattern fun (v_2606 : reg (bv 128)) (v_2607 : reg (bv 128)) (v_2608 : reg (bv 128)) => do
      v_4842 <- getRegister v_2607;
      v_4844 <- eval (extract v_4842 96 128);
      v_4845 <- getRegister v_2606;
      v_4846 <- eval (extract v_4845 96 128);
      setRegister (lhs.of_reg v_2608) (concat (extract v_4842 0 96) (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX maxcmp_single v_4844 v_4846) (expression.bv_nat 1 1)) v_4844 v_4846));
      pure ()
    pat_end;
    pattern fun (v_2601 : Mem) (v_2602 : reg (bv 128)) (v_2603 : reg (bv 128)) => do
      v_10913 <- getRegister v_2602;
      v_10915 <- eval (extract v_10913 96 128);
      v_10916 <- evaluateAddress v_2601;
      v_10917 <- load v_10916 4;
      setRegister (lhs.of_reg v_2603) (concat (extract v_10913 0 96) (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX maxcmp_single v_10915 v_10917) (expression.bv_nat 1 1)) v_10915 v_10917));
      pure ()
    pat_end
