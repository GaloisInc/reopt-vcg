def vmovlps1 : instruction :=
  definst "vmovlps" $ do
    pattern fun (v_2848 : Mem) (v_2849 : reg (bv 128)) (v_2850 : reg (bv 128)) => do
      v_10329 <- getRegister v_2849;
      v_10331 <- evaluateAddress v_2848;
      v_10332 <- load v_10331 8;
      setRegister (lhs.of_reg v_2850) (concat (extract v_10329 0 64) v_10332);
      pure ()
    pat_end;
    pattern fun (v_2845 : reg (bv 128)) (v_2844 : Mem) => do
      v_12752 <- evaluateAddress v_2844;
      v_12753 <- getRegister v_2845;
      store v_12752 (extract v_12753 64 128) 8;
      pure ()
    pat_end
