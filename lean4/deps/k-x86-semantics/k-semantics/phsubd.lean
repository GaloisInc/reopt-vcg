def phsubd1 : instruction :=
  definst "phsubd" $ do
    pattern fun (v_2555 : reg (bv 128)) (v_2556 : reg (bv 128)) => do
      v_4310 <- getRegister v_2555;
      v_4318 <- getRegister v_2556;
      setRegister (lhs.of_reg v_2556) (concat (concat (concat (sub (extract v_4310 32 64) (extract v_4310 0 32)) (sub (extract v_4310 96 128) (extract v_4310 64 96))) (sub (extract v_4318 32 64) (extract v_4318 0 32))) (sub (extract v_4318 96 128) (extract v_4318 64 96)));
      pure ()
    pat_end;
    pattern fun (v_2551 : Mem) (v_2552 : reg (bv 128)) => do
      v_11207 <- evaluateAddress v_2551;
      v_11208 <- load v_11207 16;
      v_11216 <- getRegister v_2552;
      setRegister (lhs.of_reg v_2552) (concat (concat (concat (sub (extract v_11208 32 64) (extract v_11208 0 32)) (sub (extract v_11208 96 128) (extract v_11208 64 96))) (sub (extract v_11216 32 64) (extract v_11216 0 32))) (sub (extract v_11216 96 128) (extract v_11216 64 96)));
      pure ()
    pat_end
