def vminsd1 : instruction :=
  definst "vminsd" $ do
    pattern fun (v_2737 : reg (bv 128)) (v_2738 : reg (bv 128)) (v_2739 : reg (bv 128)) => do
      v_4705 <- getRegister v_2738;
      v_4707 <- eval (extract v_4705 64 128);
      v_4708 <- getRegister v_2737;
      v_4709 <- eval (extract v_4708 64 128);
      setRegister (lhs.of_reg v_2739) (concat (extract v_4705 0 64) (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX mincmp_double v_4707 v_4709) (expression.bv_nat 1 1)) v_4707 v_4709));
      pure ()
    pat_end;
    pattern fun (v_2732 : Mem) (v_2733 : reg (bv 128)) (v_2734 : reg (bv 128)) => do
      v_10131 <- getRegister v_2733;
      v_10133 <- eval (extract v_10131 64 128);
      v_10134 <- evaluateAddress v_2732;
      v_10135 <- load v_10134 8;
      setRegister (lhs.of_reg v_2734) (concat (extract v_10131 0 64) (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX mincmp_double v_10133 v_10135) (expression.bv_nat 1 1)) v_10133 v_10135));
      pure ()
    pat_end
