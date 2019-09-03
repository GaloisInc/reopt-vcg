def movbel1 : instruction :=
  definst "movbel" $ do
    pattern fun (v_3200 : reg (bv 32)) (v_3199 : Mem) => do
      v_7681 <- evaluateAddress v_3199;
      v_7682 <- getRegister v_3200;
      store v_7681 (concat (concat (concat (extract v_7682 24 32) (extract v_7682 16 24)) (extract v_7682 8 16)) (extract v_7682 0 8)) 4;
      pure ()
    pat_end;
    pattern fun (v_3207 : Mem) (v_3208 : reg (bv 32)) => do
      v_9329 <- evaluateAddress v_3207;
      v_9330 <- load v_9329 4;
      setRegister (lhs.of_reg v_3208) (concat (concat (concat (extract v_9330 24 32) (extract v_9330 16 24)) (extract v_9330 8 16)) (extract v_9330 0 8));
      pure ()
    pat_end
