def movlps1 : instruction :=
  definst "movlps" $ do
    pattern fun (v_2506 : reg (bv 128)) (v_2505 : Mem) => do
      v_8609 <- evaluateAddress v_2505;
      v_8610 <- getRegister v_2506;
      store v_8609 (extract v_8610 64 128) 8;
      pure ()
    pat_end;
    pattern fun (v_2509 : Mem) (v_2510 : reg (bv 128)) => do
      v_8870 <- getRegister v_2510;
      v_8872 <- evaluateAddress v_2509;
      v_8873 <- load v_8872 8;
      setRegister (lhs.of_reg v_2510) (concat (extract v_8870 0 64) v_8873);
      pure ()
    pat_end
