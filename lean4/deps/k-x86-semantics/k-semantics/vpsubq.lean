def vpsubq1 : instruction :=
  definst "vpsubq" $ do
    pattern fun (v_2440 : reg (bv 128)) (v_2441 : reg (bv 128)) (v_2442 : reg (bv 128)) => do
      v_4196 <- getRegister v_2441;
      v_4198 <- getRegister v_2440;
      setRegister (lhs.of_reg v_2442) (concat (sub (extract v_4196 0 64) (extract v_4198 0 64)) (sub (extract v_4196 64 128) (extract v_4198 64 128)));
      pure ()
    pat_end;
    pattern fun (v_2451 : reg (bv 256)) (v_2452 : reg (bv 256)) (v_2453 : reg (bv 256)) => do
      v_4211 <- getRegister v_2452;
      v_4213 <- getRegister v_2451;
      setRegister (lhs.of_reg v_2453) (concat (sub (extract v_4211 0 64) (extract v_4213 0 64)) (concat (sub (extract v_4211 64 128) (extract v_4213 64 128)) (concat (sub (extract v_4211 128 192) (extract v_4213 128 192)) (sub (extract v_4211 192 256) (extract v_4213 192 256)))));
      pure ()
    pat_end;
    pattern fun (v_2435 : Mem) (v_2436 : reg (bv 128)) (v_2437 : reg (bv 128)) => do
      v_10713 <- getRegister v_2436;
      v_10715 <- evaluateAddress v_2435;
      v_10716 <- load v_10715 16;
      setRegister (lhs.of_reg v_2437) (concat (sub (extract v_10713 0 64) (extract v_10716 0 64)) (sub (extract v_10713 64 128) (extract v_10716 64 128)));
      pure ()
    pat_end;
    pattern fun (v_2446 : Mem) (v_2447 : reg (bv 256)) (v_2448 : reg (bv 256)) => do
      v_10724 <- getRegister v_2447;
      v_10726 <- evaluateAddress v_2446;
      v_10727 <- load v_10726 32;
      setRegister (lhs.of_reg v_2448) (concat (sub (extract v_10724 0 64) (extract v_10727 0 64)) (concat (sub (extract v_10724 64 128) (extract v_10727 64 128)) (concat (sub (extract v_10724 128 192) (extract v_10727 128 192)) (sub (extract v_10724 192 256) (extract v_10727 192 256)))));
      pure ()
    pat_end
