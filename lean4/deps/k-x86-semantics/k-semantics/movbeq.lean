def movbeq1 : instruction :=
  definst "movbeq" $ do
    pattern fun (v_3216 : reg (bv 64)) (v_3215 : Mem) => do
      v_7699 <- evaluateAddress v_3215;
      v_7700 <- getRegister v_3216;
      store v_7699 (concat (concat (concat (concat (concat (concat (concat (extract v_7700 56 64) (extract v_7700 48 56)) (extract v_7700 40 48)) (extract v_7700 32 40)) (extract v_7700 24 32)) (extract v_7700 16 24)) (extract v_7700 8 16)) (extract v_7700 0 8)) 8;
      pure ()
    pat_end;
    pattern fun (v_3223 : Mem) (v_3224 : reg (bv 64)) => do
      v_9358 <- evaluateAddress v_3223;
      v_9359 <- load v_9358 8;
      setRegister (lhs.of_reg v_3224) (concat (concat (concat (concat (concat (concat (concat (extract v_9359 56 64) (extract v_9359 48 56)) (extract v_9359 40 48)) (extract v_9359 32 40)) (extract v_9359 24 32)) (extract v_9359 16 24)) (extract v_9359 8 16)) (extract v_9359 0 8));
      pure ()
    pat_end
