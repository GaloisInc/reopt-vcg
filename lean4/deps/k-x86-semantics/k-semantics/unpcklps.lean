def unpcklps1 : instruction :=
  definst "unpcklps" $ do
    pattern fun (v_2573 : reg (bv 128)) (v_2574 : reg (bv 128)) => do
      v_4809 <- getRegister v_2573;
      v_4811 <- getRegister v_2574;
      setRegister (lhs.of_reg v_2574) (concat (concat (concat (extract v_4809 64 96) (extract v_4811 64 96)) (extract v_4809 96 128)) (extract v_4811 96 128));
      pure ()
    pat_end;
    pattern fun (v_2566 : Mem) (v_2569 : reg (bv 128)) => do
      v_10365 <- evaluateAddress v_2566;
      v_10366 <- load v_10365 16;
      v_10368 <- getRegister v_2569;
      setRegister (lhs.of_reg v_2569) (concat (concat (concat (extract v_10366 64 96) (extract v_10368 64 96)) (extract v_10366 96 128)) (extract v_10368 96 128));
      pure ()
    pat_end
