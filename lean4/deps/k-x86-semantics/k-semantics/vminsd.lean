def vminsd1 : instruction :=
  definst "vminsd" $ do
    pattern fun (v_2649 : reg (bv 128)) (v_2650 : reg (bv 128)) (v_2651 : reg (bv 128)) => do
      v_4620 <- getRegister v_2650;
      v_4622 <- eval (extract v_4620 64 128);
      v_4623 <- getRegister v_2649;
      v_4624 <- eval (extract v_4623 64 128);
      setRegister (lhs.of_reg v_2651) (concat (extract v_4620 0 64) (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX mincmp_double v_4622 v_4624) (expression.bv_nat 1 1)) v_4622 v_4624));
      pure ()
    pat_end;
    pattern fun (v_2643 : Mem) (v_2644 : reg (bv 128)) (v_2645 : reg (bv 128)) => do
      v_10238 <- getRegister v_2644;
      v_10240 <- eval (extract v_10238 64 128);
      v_10241 <- evaluateAddress v_2643;
      v_10242 <- load v_10241 8;
      setRegister (lhs.of_reg v_2645) (concat (extract v_10238 0 64) (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX mincmp_double v_10240 v_10242) (expression.bv_nat 1 1)) v_10240 v_10242));
      pure ()
    pat_end
