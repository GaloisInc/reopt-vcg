def movlhps1 : instruction :=
  definst "movlhps" $ do
    pattern fun (v_2581 : reg (bv 128)) (v_2582 : reg (bv 128)) => do
      v_3999 <- getRegister v_2581;
      v_4001 <- getRegister v_2582;
      setRegister (lhs.of_reg v_2582) (concat (extract v_3999 64 128) (extract v_4001 64 128));
      pure ()
    pat_end
