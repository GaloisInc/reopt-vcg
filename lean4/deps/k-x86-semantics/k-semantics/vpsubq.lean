def vpsubq1 : instruction :=
  definst "vpsubq" $ do
    pattern fun (v_2494 : reg (bv 128)) (v_2495 : reg (bv 128)) (v_2496 : reg (bv 128)) => do
      v_4247 <- getRegister v_2495;
      v_4249 <- getRegister v_2494;
      setRegister (lhs.of_reg v_2496) (concat (sub (extract v_4247 0 64) (extract v_4249 0 64)) (sub (extract v_4247 64 128) (extract v_4249 64 128)));
      pure ()
    pat_end;
    pattern fun (v_2505 : reg (bv 256)) (v_2506 : reg (bv 256)) (v_2507 : reg (bv 256)) => do
      v_4262 <- getRegister v_2506;
      v_4264 <- getRegister v_2505;
      setRegister (lhs.of_reg v_2507) (concat (sub (extract v_4262 0 64) (extract v_4264 0 64)) (concat (sub (extract v_4262 64 128) (extract v_4264 64 128)) (concat (sub (extract v_4262 128 192) (extract v_4264 128 192)) (sub (extract v_4262 192 256) (extract v_4264 192 256)))));
      pure ()
    pat_end;
    pattern fun (v_2488 : Mem) (v_2489 : reg (bv 128)) (v_2490 : reg (bv 128)) => do
      v_10391 <- getRegister v_2489;
      v_10393 <- evaluateAddress v_2488;
      v_10394 <- load v_10393 16;
      setRegister (lhs.of_reg v_2490) (concat (sub (extract v_10391 0 64) (extract v_10394 0 64)) (sub (extract v_10391 64 128) (extract v_10394 64 128)));
      pure ()
    pat_end;
    pattern fun (v_2499 : Mem) (v_2500 : reg (bv 256)) (v_2501 : reg (bv 256)) => do
      v_10402 <- getRegister v_2500;
      v_10404 <- evaluateAddress v_2499;
      v_10405 <- load v_10404 32;
      setRegister (lhs.of_reg v_2501) (concat (sub (extract v_10402 0 64) (extract v_10405 0 64)) (concat (sub (extract v_10402 64 128) (extract v_10405 64 128)) (concat (sub (extract v_10402 128 192) (extract v_10405 128 192)) (sub (extract v_10402 192 256) (extract v_10405 192 256)))));
      pure ()
    pat_end
