def vmovhps1 : instruction :=
  definst "vmovhps" $ do
    pattern fun (v_2837 : Mem) (v_2838 : reg (bv 128)) (v_2839 : reg (bv 128)) => do
      v_11120 <- evaluateAddress v_2837;
      v_11121 <- load v_11120 8;
      v_11122 <- getRegister v_2838;
      setRegister (lhs.of_reg v_2839) (concat v_11121 (extract v_11122 64 128));
      pure ()
    pat_end;
    pattern fun (v_2834 : reg (bv 128)) (v_2833 : Mem) => do
      v_13621 <- evaluateAddress v_2833;
      v_13622 <- getRegister v_2834;
      store v_13621 (extract v_13622 0 64) 8;
      pure ()
    pat_end
