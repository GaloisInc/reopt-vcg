def maxss1 : instruction :=
  definst "maxss" $ do
    pattern fun (v_3143 : reg (bv 128)) (v_3144 : reg (bv 128)) => do
      v_5623 <- getRegister v_3144;
      v_5625 <- eval (extract v_5623 96 128);
      v_5626 <- getRegister v_3143;
      v_5627 <- eval (extract v_5626 96 128);
      setRegister (lhs.of_reg v_3144) (concat (extract v_5623 0 96) (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX maxcmp_single v_5625 v_5627) (expression.bv_nat 1 1)) v_5625 v_5627));
      pure ()
    pat_end;
    pattern fun (v_3138 : Mem) (v_3139 : reg (bv 128)) => do
      v_8874 <- getRegister v_3139;
      v_8876 <- eval (extract v_8874 96 128);
      v_8877 <- evaluateAddress v_3138;
      v_8878 <- load v_8877 4;
      setRegister (lhs.of_reg v_3139) (concat (extract v_8874 0 96) (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX maxcmp_single v_8876 v_8878) (expression.bv_nat 1 1)) v_8876 v_8878));
      pure ()
    pat_end
