def movlpd1 : instruction :=
  definst "movlpd" $ do
    pattern fun (v_2587 : reg (bv 128)) (v_2586 : Mem) => do
      v_8475 <- evaluateAddress v_2586;
      v_8476 <- getRegister v_2587;
      store v_8475 (extract v_8476 64 128) 8;
      pure ()
    pat_end;
    pattern fun (v_2590 : Mem) (v_2591 : reg (bv 128)) => do
      v_8734 <- getRegister v_2591;
      v_8736 <- evaluateAddress v_2590;
      v_8737 <- load v_8736 8;
      setRegister (lhs.of_reg v_2591) (concat (extract v_8734 0 64) v_8737);
      pure ()
    pat_end
