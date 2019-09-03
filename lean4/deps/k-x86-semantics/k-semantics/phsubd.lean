def phsubd1 : instruction :=
  definst "phsubd" $ do
    pattern fun (v_2478 : reg (bv 128)) (v_2479 : reg (bv 128)) => do
      v_4232 <- getRegister v_2478;
      v_4240 <- getRegister v_2479;
      setRegister (lhs.of_reg v_2479) (concat (concat (concat (sub (extract v_4232 32 64) (extract v_4232 0 32)) (sub (extract v_4232 96 128) (extract v_4232 64 96))) (sub (extract v_4240 32 64) (extract v_4240 0 32))) (sub (extract v_4240 96 128) (extract v_4240 64 96)));
      pure ()
    pat_end;
    pattern fun (v_2474 : Mem) (v_2475 : reg (bv 128)) => do
      v_11354 <- evaluateAddress v_2474;
      v_11355 <- load v_11354 16;
      v_11363 <- getRegister v_2475;
      setRegister (lhs.of_reg v_2475) (concat (concat (concat (sub (extract v_11355 32 64) (extract v_11355 0 32)) (sub (extract v_11355 96 128) (extract v_11355 64 96))) (sub (extract v_11363 32 64) (extract v_11363 0 32))) (sub (extract v_11363 96 128) (extract v_11363 64 96)));
      pure ()
    pat_end
