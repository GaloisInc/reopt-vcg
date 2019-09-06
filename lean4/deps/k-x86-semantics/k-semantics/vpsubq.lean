def vpsubq1 : instruction :=
  definst "vpsubq" $ do
    pattern fun (v_2521 : reg (bv 128)) (v_2522 : reg (bv 128)) (v_2523 : reg (bv 128)) => do
      v_4274 <- getRegister v_2522;
      v_4276 <- getRegister v_2521;
      setRegister (lhs.of_reg v_2523) (concat (sub (extract v_4274 0 64) (extract v_4276 0 64)) (sub (extract v_4274 64 128) (extract v_4276 64 128)));
      pure ()
    pat_end;
    pattern fun (v_2532 : reg (bv 256)) (v_2533 : reg (bv 256)) (v_2534 : reg (bv 256)) => do
      v_4289 <- getRegister v_2533;
      v_4291 <- getRegister v_2532;
      setRegister (lhs.of_reg v_2534) (concat (sub (extract v_4289 0 64) (extract v_4291 0 64)) (concat (sub (extract v_4289 64 128) (extract v_4291 64 128)) (concat (sub (extract v_4289 128 192) (extract v_4291 128 192)) (sub (extract v_4289 192 256) (extract v_4291 192 256)))));
      pure ()
    pat_end;
    pattern fun (v_2515 : Mem) (v_2516 : reg (bv 128)) (v_2517 : reg (bv 128)) => do
      v_10418 <- getRegister v_2516;
      v_10420 <- evaluateAddress v_2515;
      v_10421 <- load v_10420 16;
      setRegister (lhs.of_reg v_2517) (concat (sub (extract v_10418 0 64) (extract v_10421 0 64)) (sub (extract v_10418 64 128) (extract v_10421 64 128)));
      pure ()
    pat_end;
    pattern fun (v_2526 : Mem) (v_2527 : reg (bv 256)) (v_2528 : reg (bv 256)) => do
      v_10429 <- getRegister v_2527;
      v_10431 <- evaluateAddress v_2526;
      v_10432 <- load v_10431 32;
      setRegister (lhs.of_reg v_2528) (concat (sub (extract v_10429 0 64) (extract v_10432 0 64)) (concat (sub (extract v_10429 64 128) (extract v_10432 64 128)) (concat (sub (extract v_10429 128 192) (extract v_10432 128 192)) (sub (extract v_10429 192 256) (extract v_10432 192 256)))));
      pure ()
    pat_end
