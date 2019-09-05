def movbel1 : instruction :=
  definst "movbel" $ do
    pattern fun (v_3264 : reg (bv 32)) (v_3263 : Mem) => do
      v_7513 <- evaluateAddress v_3263;
      v_7514 <- getRegister v_3264;
      store v_7513 (concat (concat (concat (extract v_7514 24 32) (extract v_7514 16 24)) (extract v_7514 8 16)) (extract v_7514 0 8)) 4;
      pure ()
    pat_end;
    pattern fun (v_3271 : Mem) (v_3272 : reg (bv 32)) => do
      v_8969 <- evaluateAddress v_3271;
      v_8970 <- load v_8969 4;
      setRegister (lhs.of_reg v_3272) (concat (concat (concat (extract v_8970 24 32) (extract v_8970 16 24)) (extract v_8970 8 16)) (extract v_8970 0 8));
      pure ()
    pat_end
