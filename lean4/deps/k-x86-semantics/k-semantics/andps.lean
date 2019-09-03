def andps1 : instruction :=
  definst "andps" $ do
    pattern fun (v_2832 : reg (bv 128)) (v_2833 : reg (bv 128)) => do
      v_5459 <- getRegister v_2833;
      v_5460 <- getRegister v_2832;
      setRegister (lhs.of_reg v_2833) (bv_and v_5459 v_5460);
      pure ()
    pat_end;
    pattern fun (v_2827 : Mem) (v_2828 : reg (bv 128)) => do
      v_9402 <- getRegister v_2828;
      v_9403 <- evaluateAddress v_2827;
      v_9404 <- load v_9403 16;
      setRegister (lhs.of_reg v_2828) (bv_and v_9402 v_9404);
      pure ()
    pat_end
