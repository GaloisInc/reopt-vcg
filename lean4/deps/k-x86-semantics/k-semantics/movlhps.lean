def movlhps1 : instruction :=
  definst "movlhps" $ do
    pattern fun (v_2556 : reg (bv 128)) (v_2557 : reg (bv 128)) => do
      v_3972 <- getRegister v_2556;
      v_3974 <- getRegister v_2557;
      setRegister (lhs.of_reg v_2557) (concat (extract v_3972 64 128) (extract v_3974 64 128));
      pure ()
    pat_end
