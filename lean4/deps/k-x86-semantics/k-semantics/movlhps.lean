def movlhps1 : instruction :=
  definst "movlhps" $ do
    pattern fun (v_2505 : reg (bv 128)) (v_2506 : reg (bv 128)) => do
      v_3921 <- getRegister v_2505;
      v_3923 <- getRegister v_2506;
      setRegister (lhs.of_reg v_2506) (concat (extract v_3921 64 128) (extract v_3923 64 128));
      pure ()
    pat_end
