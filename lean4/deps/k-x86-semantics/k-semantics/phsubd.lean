def phsubd1 : instruction :=
  definst "phsubd" $ do
    pattern fun (v_2527 : reg (bv 128)) (v_2528 : reg (bv 128)) => do
      v_4283 <- getRegister v_2527;
      v_4291 <- getRegister v_2528;
      setRegister (lhs.of_reg v_2528) (concat (concat (concat (sub (extract v_4283 32 64) (extract v_4283 0 32)) (sub (extract v_4283 96 128) (extract v_4283 64 96))) (sub (extract v_4291 32 64) (extract v_4291 0 32))) (sub (extract v_4291 96 128) (extract v_4291 64 96)));
      pure ()
    pat_end;
    pattern fun (v_2524 : Mem) (v_2523 : reg (bv 128)) => do
      v_11231 <- evaluateAddress v_2524;
      v_11232 <- load v_11231 16;
      v_11240 <- getRegister v_2523;
      setRegister (lhs.of_reg v_2523) (concat (concat (concat (sub (extract v_11232 32 64) (extract v_11232 0 32)) (sub (extract v_11232 96 128) (extract v_11232 64 96))) (sub (extract v_11240 32 64) (extract v_11240 0 32))) (sub (extract v_11240 96 128) (extract v_11240 64 96)));
      pure ()
    pat_end
