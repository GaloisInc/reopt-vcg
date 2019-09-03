def vpsubq1 : instruction :=
  definst "vpsubq" $ do
    pattern fun (v_2430 : reg (bv 128)) (v_2431 : reg (bv 128)) (v_2432 : reg (bv 128)) => do
      v_4183 <- getRegister v_2431;
      v_4185 <- getRegister v_2430;
      setRegister (lhs.of_reg v_2432) (concat (sub (extract v_4183 0 64) (extract v_4185 0 64)) (sub (extract v_4183 64 128) (extract v_4185 64 128)));
      pure ()
    pat_end;
    pattern fun (v_2440 : reg (bv 256)) (v_2441 : reg (bv 256)) (v_2442 : reg (bv 256)) => do
      v_4198 <- getRegister v_2441;
      v_4200 <- getRegister v_2440;
      setRegister (lhs.of_reg v_2442) (concat (sub (extract v_4198 0 64) (extract v_4200 0 64)) (concat (sub (extract v_4198 64 128) (extract v_4200 64 128)) (concat (sub (extract v_4198 128 192) (extract v_4200 128 192)) (sub (extract v_4198 192 256) (extract v_4200 192 256)))));
      pure ()
    pat_end;
    pattern fun (v_2424 : Mem) (v_2425 : reg (bv 128)) (v_2426 : reg (bv 128)) => do
      v_10568 <- getRegister v_2425;
      v_10570 <- evaluateAddress v_2424;
      v_10571 <- load v_10570 16;
      setRegister (lhs.of_reg v_2426) (concat (sub (extract v_10568 0 64) (extract v_10571 0 64)) (sub (extract v_10568 64 128) (extract v_10571 64 128)));
      pure ()
    pat_end;
    pattern fun (v_2435 : Mem) (v_2436 : reg (bv 256)) (v_2437 : reg (bv 256)) => do
      v_10579 <- getRegister v_2436;
      v_10581 <- evaluateAddress v_2435;
      v_10582 <- load v_10581 32;
      setRegister (lhs.of_reg v_2437) (concat (sub (extract v_10579 0 64) (extract v_10582 0 64)) (concat (sub (extract v_10579 64 128) (extract v_10582 64 128)) (concat (sub (extract v_10579 128 192) (extract v_10582 128 192)) (sub (extract v_10579 192 256) (extract v_10582 192 256)))));
      pure ()
    pat_end
