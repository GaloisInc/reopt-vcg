def phaddw1 : instruction :=
  definst "phaddw" $ do
    pattern fun (v_2509 : reg (bv 128)) (v_2510 : reg (bv 128)) => do
      v_4209 <- getRegister v_2509;
      v_4225 <- getRegister v_2510;
      setRegister (lhs.of_reg v_2510) (concat (concat (concat (concat (concat (concat (concat (add (extract v_4209 0 16) (extract v_4209 16 32)) (add (extract v_4209 32 48) (extract v_4209 48 64))) (add (extract v_4209 64 80) (extract v_4209 80 96))) (add (extract v_4209 96 112) (extract v_4209 112 128))) (add (extract v_4225 0 16) (extract v_4225 16 32))) (add (extract v_4225 32 48) (extract v_4225 48 64))) (add (extract v_4225 64 80) (extract v_4225 80 96))) (add (extract v_4225 96 112) (extract v_4225 112 128)));
      pure ()
    pat_end;
    pattern fun (v_2506 : Mem) (v_2505 : reg (bv 128)) => do
      v_11163 <- evaluateAddress v_2506;
      v_11164 <- load v_11163 16;
      v_11180 <- getRegister v_2505;
      setRegister (lhs.of_reg v_2505) (concat (concat (concat (concat (concat (concat (concat (add (extract v_11164 0 16) (extract v_11164 16 32)) (add (extract v_11164 32 48) (extract v_11164 48 64))) (add (extract v_11164 64 80) (extract v_11164 80 96))) (add (extract v_11164 96 112) (extract v_11164 112 128))) (add (extract v_11180 0 16) (extract v_11180 16 32))) (add (extract v_11180 32 48) (extract v_11180 48 64))) (add (extract v_11180 64 80) (extract v_11180 80 96))) (add (extract v_11180 96 112) (extract v_11180 112 128)));
      pure ()
    pat_end
