def vmaxss1 : instruction :=
  definst "vmaxss" $ do
    pattern fun (v_2594 : reg (bv 128)) (v_2595 : reg (bv 128)) (v_2596 : reg (bv 128)) => do
      v_4469 <- getRegister v_2595;
      v_4471 <- eval (extract v_4469 96 128);
      v_4472 <- getRegister v_2594;
      v_4473 <- eval (extract v_4472 96 128);
      setRegister (lhs.of_reg v_2596) (concat (extract v_4469 0 96) (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX maxcmp_single v_4471 v_4473) (expression.bv_nat 1 1)) v_4471 v_4473));
      pure ()
    pat_end;
    pattern fun (v_2588 : Mem) (v_2589 : reg (bv 128)) (v_2590 : reg (bv 128)) => do
      v_10108 <- getRegister v_2589;
      v_10110 <- eval (extract v_10108 96 128);
      v_10111 <- evaluateAddress v_2588;
      v_10112 <- load v_10111 4;
      setRegister (lhs.of_reg v_2590) (concat (extract v_10108 0 96) (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX maxcmp_single v_10110 v_10112) (expression.bv_nat 1 1)) v_10110 v_10112));
      pure ()
    pat_end
