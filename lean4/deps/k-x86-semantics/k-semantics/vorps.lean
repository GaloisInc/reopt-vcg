def vorps1 : instruction :=
  definst "vorps" $ do
    pattern fun (v_3216 : Mem) (v_3217 : reg (bv 128)) (v_3218 : reg (bv 128)) => do
      v_10456 <- getRegister v_3217;
      v_10457 <- evaluateAddress v_3216;
      v_10458 <- load v_10457 16;
      setRegister (lhs.of_reg v_3218) (bv_or v_10456 v_10458);
      pure ()
    pat_end;
    pattern fun (v_3227 : Mem) (v_3228 : reg (bv 256)) (v_3229 : reg (bv 256)) => do
      v_10461 <- getRegister v_3228;
      v_10462 <- evaluateAddress v_3227;
      v_10463 <- load v_10462 32;
      setRegister (lhs.of_reg v_3229) (bv_or v_10461 v_10463);
      pure ()
    pat_end
