def maxpd1 : instruction :=
  definst "maxpd" $ do
    pattern fun (v_3051 : reg (bv 128)) (v_3052 : reg (bv 128)) => do
      v_5729 <- getRegister v_3052;
      v_5730 <- eval (extract v_5729 0 64);
      v_5731 <- getRegister v_3051;
      v_5732 <- eval (extract v_5731 0 64);
      v_5736 <- eval (extract v_5729 64 128);
      v_5737 <- eval (extract v_5731 64 128);
      setRegister (lhs.of_reg v_3052) (concat (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX maxcmp_double v_5730 v_5732) (expression.bv_nat 1 1)) v_5730 v_5732) (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX maxcmp_double v_5736 v_5737) (expression.bv_nat 1 1)) v_5736 v_5737));
      pure ()
    pat_end;
    pattern fun (v_3047 : Mem) (v_3048 : reg (bv 128)) => do
      v_9182 <- getRegister v_3048;
      v_9183 <- eval (extract v_9182 0 64);
      v_9184 <- evaluateAddress v_3047;
      v_9185 <- load v_9184 16;
      v_9186 <- eval (extract v_9185 0 64);
      v_9190 <- eval (extract v_9182 64 128);
      v_9191 <- eval (extract v_9185 64 128);
      setRegister (lhs.of_reg v_3048) (concat (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX maxcmp_double v_9183 v_9186) (expression.bv_nat 1 1)) v_9183 v_9186) (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX maxcmp_double v_9190 v_9191) (expression.bv_nat 1 1)) v_9190 v_9191));
      pure ()
    pat_end
