def phaddw1 : instruction :=
  definst "phaddw" $ do
    pattern fun (v_2460 : reg (bv 128)) (v_2461 : reg (bv 128)) => do
      v_4158 <- getRegister v_2460;
      v_4174 <- getRegister v_2461;
      setRegister (lhs.of_reg v_2461) (concat (concat (concat (concat (concat (concat (concat (add (extract v_4158 0 16) (extract v_4158 16 32)) (add (extract v_4158 32 48) (extract v_4158 48 64))) (add (extract v_4158 64 80) (extract v_4158 80 96))) (add (extract v_4158 96 112) (extract v_4158 112 128))) (add (extract v_4174 0 16) (extract v_4174 16 32))) (add (extract v_4174 32 48) (extract v_4174 48 64))) (add (extract v_4174 64 80) (extract v_4174 80 96))) (add (extract v_4174 96 112) (extract v_4174 112 128)));
      pure ()
    pat_end;
    pattern fun (v_2456 : Mem) (v_2457 : reg (bv 128)) => do
      v_11286 <- evaluateAddress v_2456;
      v_11287 <- load v_11286 16;
      v_11303 <- getRegister v_2457;
      setRegister (lhs.of_reg v_2457) (concat (concat (concat (concat (concat (concat (concat (add (extract v_11287 0 16) (extract v_11287 16 32)) (add (extract v_11287 32 48) (extract v_11287 48 64))) (add (extract v_11287 64 80) (extract v_11287 80 96))) (add (extract v_11287 96 112) (extract v_11287 112 128))) (add (extract v_11303 0 16) (extract v_11303 16 32))) (add (extract v_11303 32 48) (extract v_11303 48 64))) (add (extract v_11303 64 80) (extract v_11303 80 96))) (add (extract v_11303 96 112) (extract v_11303 112 128)));
      pure ()
    pat_end
