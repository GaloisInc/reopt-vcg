def movhlps1 : instruction :=
  definst "movhlps" $ do
    pattern fun (v_2538 : reg (bv 128)) (v_2539 : reg (bv 128)) => do
      v_3961 <- getRegister v_2539;
      v_3963 <- getRegister v_2538;
      setRegister (lhs.of_reg v_2539) (concat (extract v_3961 0 64) (extract v_3963 0 64));
      pure ()
    pat_end
