def vxorps1 : instruction :=
  definst "vxorps" $ do
    pattern fun (v_3331 : Mem) (v_3332 : reg (bv 128)) (v_3333 : reg (bv 128)) => do
      v_13529 <- getRegister v_3332;
      v_13530 <- evaluateAddress v_3331;
      v_13531 <- load v_13530 16;
      setRegister (lhs.of_reg v_3333) (bv_xor v_13529 v_13531);
      pure ()
    pat_end;
    pattern fun (v_3342 : Mem) (v_3343 : reg (bv 256)) (v_3344 : reg (bv 256)) => do
      v_13534 <- getRegister v_3343;
      v_13535 <- evaluateAddress v_3342;
      v_13536 <- load v_13535 32;
      setRegister (lhs.of_reg v_3344) (bv_xor v_13534 v_13536);
      pure ()
    pat_end
