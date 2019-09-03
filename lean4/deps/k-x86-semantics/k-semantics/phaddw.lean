def phaddw1 : instruction :=
  definst "phaddw" $ do
    pattern fun (v_2446 : reg (bv 128)) (v_2447 : reg (bv 128)) => do
      v_4161 <- getRegister v_2446;
      v_4177 <- getRegister v_2447;
      setRegister (lhs.of_reg v_2447) (concat (concat (concat (concat (concat (concat (concat (add (extract v_4161 0 16) (extract v_4161 16 32)) (add (extract v_4161 32 48) (extract v_4161 48 64))) (add (extract v_4161 64 80) (extract v_4161 80 96))) (add (extract v_4161 96 112) (extract v_4161 112 128))) (add (extract v_4177 0 16) (extract v_4177 16 32))) (add (extract v_4177 32 48) (extract v_4177 48 64))) (add (extract v_4177 64 80) (extract v_4177 80 96))) (add (extract v_4177 96 112) (extract v_4177 112 128)));
      pure ()
    pat_end;
    pattern fun (v_2441 : Mem) (v_2442 : reg (bv 128)) => do
      v_11619 <- evaluateAddress v_2441;
      v_11620 <- load v_11619 16;
      v_11636 <- getRegister v_2442;
      setRegister (lhs.of_reg v_2442) (concat (concat (concat (concat (concat (concat (concat (add (extract v_11620 0 16) (extract v_11620 16 32)) (add (extract v_11620 32 48) (extract v_11620 48 64))) (add (extract v_11620 64 80) (extract v_11620 80 96))) (add (extract v_11620 96 112) (extract v_11620 112 128))) (add (extract v_11636 0 16) (extract v_11636 16 32))) (add (extract v_11636 32 48) (extract v_11636 48 64))) (add (extract v_11636 64 80) (extract v_11636 80 96))) (add (extract v_11636 96 112) (extract v_11636 112 128)));
      pure ()
    pat_end
