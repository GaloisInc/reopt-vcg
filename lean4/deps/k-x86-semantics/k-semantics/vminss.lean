def vminss1 : instruction :=
  definst "vminss" $ do
    pattern fun (v_2660 : reg (bv 128)) (v_2661 : reg (bv 128)) (v_2662 : reg (bv 128)) => do
      v_4635 <- getRegister v_2661;
      v_4637 <- eval (extract v_4635 96 128);
      v_4638 <- getRegister v_2660;
      v_4639 <- eval (extract v_4638 96 128);
      setRegister (lhs.of_reg v_2662) (concat (extract v_4635 0 96) (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX mincmp_single v_4637 v_4639) (expression.bv_nat 1 1)) v_4637 v_4639));
      pure ()
    pat_end;
    pattern fun (v_2654 : Mem) (v_2655 : reg (bv 128)) (v_2656 : reg (bv 128)) => do
      v_10248 <- getRegister v_2655;
      v_10250 <- eval (extract v_10248 96 128);
      v_10251 <- evaluateAddress v_2654;
      v_10252 <- load v_10251 4;
      setRegister (lhs.of_reg v_2656) (concat (extract v_10248 0 96) (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX mincmp_single v_10250 v_10252) (expression.bv_nat 1 1)) v_10250 v_10252));
      pure ()
    pat_end
