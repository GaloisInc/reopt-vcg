def vminpd1 : instruction :=
  definst "vminpd" $ do
    pattern fun (v_2668 : reg (bv 128)) (v_2669 : reg (bv 128)) (v_2670 : reg (bv 128)) => do
      v_4542 <- getRegister v_2669;
      v_4543 <- eval (extract v_4542 0 64);
      v_4544 <- getRegister v_2668;
      v_4545 <- eval (extract v_4544 0 64);
      v_4549 <- eval (extract v_4542 64 128);
      v_4550 <- eval (extract v_4544 64 128);
      setRegister (lhs.of_reg v_2670) (concat (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX mincmp_double v_4543 v_4545) (expression.bv_nat 1 1)) v_4543 v_4545) (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX mincmp_double v_4549 v_4550) (expression.bv_nat 1 1)) v_4549 v_4550));
      pure ()
    pat_end;
    pattern fun (v_2680 : reg (bv 256)) (v_2681 : reg (bv 256)) (v_2682 : reg (bv 256)) => do
      v_4561 <- getRegister v_2681;
      v_4562 <- eval (extract v_4561 0 64);
      v_4563 <- getRegister v_2680;
      v_4564 <- eval (extract v_4563 0 64);
      v_4568 <- eval (extract v_4561 64 128);
      v_4569 <- eval (extract v_4563 64 128);
      v_4573 <- eval (extract v_4561 128 192);
      v_4574 <- eval (extract v_4563 128 192);
      v_4578 <- eval (extract v_4561 192 256);
      v_4579 <- eval (extract v_4563 192 256);
      setRegister (lhs.of_reg v_2682) (concat (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX mincmp_double v_4562 v_4564) (expression.bv_nat 1 1)) v_4562 v_4564) (concat (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX mincmp_double v_4568 v_4569) (expression.bv_nat 1 1)) v_4568 v_4569) (concat (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX mincmp_double v_4573 v_4574) (expression.bv_nat 1 1)) v_4573 v_4574) (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX mincmp_double v_4578 v_4579) (expression.bv_nat 1 1)) v_4578 v_4579))));
      pure ()
    pat_end;
    pattern fun (v_2663 : Mem) (v_2664 : reg (bv 128)) (v_2665 : reg (bv 128)) => do
      v_9984 <- getRegister v_2664;
      v_9985 <- eval (extract v_9984 0 64);
      v_9986 <- evaluateAddress v_2663;
      v_9987 <- load v_9986 16;
      v_9988 <- eval (extract v_9987 0 64);
      v_9992 <- eval (extract v_9984 64 128);
      v_9993 <- eval (extract v_9987 64 128);
      setRegister (lhs.of_reg v_2665) (concat (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX mincmp_double v_9985 v_9988) (expression.bv_nat 1 1)) v_9985 v_9988) (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX mincmp_double v_9992 v_9993) (expression.bv_nat 1 1)) v_9992 v_9993));
      pure ()
    pat_end;
    pattern fun (v_2674 : Mem) (v_2675 : reg (bv 256)) (v_2676 : reg (bv 256)) => do
      v_9999 <- getRegister v_2675;
      v_10000 <- eval (extract v_9999 0 64);
      v_10001 <- evaluateAddress v_2674;
      v_10002 <- load v_10001 32;
      v_10003 <- eval (extract v_10002 0 64);
      v_10007 <- eval (extract v_9999 64 128);
      v_10008 <- eval (extract v_10002 64 128);
      v_10012 <- eval (extract v_9999 128 192);
      v_10013 <- eval (extract v_10002 128 192);
      v_10017 <- eval (extract v_9999 192 256);
      v_10018 <- eval (extract v_10002 192 256);
      setRegister (lhs.of_reg v_2676) (concat (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX mincmp_double v_10000 v_10003) (expression.bv_nat 1 1)) v_10000 v_10003) (concat (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX mincmp_double v_10007 v_10008) (expression.bv_nat 1 1)) v_10007 v_10008) (concat (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX mincmp_double v_10012 v_10013) (expression.bv_nat 1 1)) v_10012 v_10013) (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX mincmp_double v_10017 v_10018) (expression.bv_nat 1 1)) v_10017 v_10018))));
      pure ()
    pat_end
