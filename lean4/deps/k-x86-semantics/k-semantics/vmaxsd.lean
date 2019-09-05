def vmaxsd1 : instruction :=
  definst "vmaxsd" $ do
    pattern fun (v_2646 : reg (bv 128)) (v_2647 : reg (bv 128)) (v_2648 : reg (bv 128)) => do
      v_4512 <- getRegister v_2647;
      v_4514 <- eval (extract v_4512 64 128);
      v_4515 <- getRegister v_2646;
      v_4516 <- eval (extract v_4515 64 128);
      setRegister (lhs.of_reg v_2648) (concat (extract v_4512 0 64) (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX maxcmp_double v_4514 v_4516) (expression.bv_nat 1 1)) v_4514 v_4516));
      pure ()
    pat_end;
    pattern fun (v_2641 : Mem) (v_2642 : reg (bv 128)) (v_2643 : reg (bv 128)) => do
      v_9964 <- getRegister v_2642;
      v_9966 <- eval (extract v_9964 64 128);
      v_9967 <- evaluateAddress v_2641;
      v_9968 <- load v_9967 8;
      setRegister (lhs.of_reg v_2643) (concat (extract v_9964 0 64) (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX maxcmp_double v_9966 v_9968) (expression.bv_nat 1 1)) v_9966 v_9968));
      pure ()
    pat_end
