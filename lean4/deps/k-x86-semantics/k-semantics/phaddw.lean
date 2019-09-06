def phaddw1 : instruction :=
  definst "phaddw" $ do
    pattern fun (v_2537 : reg (bv 128)) (v_2538 : reg (bv 128)) => do
      v_4236 <- getRegister v_2537;
      v_4252 <- getRegister v_2538;
      setRegister (lhs.of_reg v_2538) (concat (concat (concat (concat (concat (concat (concat (add (extract v_4236 0 16) (extract v_4236 16 32)) (add (extract v_4236 32 48) (extract v_4236 48 64))) (add (extract v_4236 64 80) (extract v_4236 80 96))) (add (extract v_4236 96 112) (extract v_4236 112 128))) (add (extract v_4252 0 16) (extract v_4252 16 32))) (add (extract v_4252 32 48) (extract v_4252 48 64))) (add (extract v_4252 64 80) (extract v_4252 80 96))) (add (extract v_4252 96 112) (extract v_4252 112 128)));
      pure ()
    pat_end;
    pattern fun (v_2533 : Mem) (v_2534 : reg (bv 128)) => do
      v_11139 <- evaluateAddress v_2533;
      v_11140 <- load v_11139 16;
      v_11156 <- getRegister v_2534;
      setRegister (lhs.of_reg v_2534) (concat (concat (concat (concat (concat (concat (concat (add (extract v_11140 0 16) (extract v_11140 16 32)) (add (extract v_11140 32 48) (extract v_11140 48 64))) (add (extract v_11140 64 80) (extract v_11140 80 96))) (add (extract v_11140 96 112) (extract v_11140 112 128))) (add (extract v_11156 0 16) (extract v_11156 16 32))) (add (extract v_11156 32 48) (extract v_11156 48 64))) (add (extract v_11156 64 80) (extract v_11156 80 96))) (add (extract v_11156 96 112) (extract v_11156 112 128)));
      pure ()
    pat_end
