def phaddd1 : instruction :=
  definst "phaddd" $ do
    pattern fun (v_2442 : reg (bv 128)) (v_2443 : reg (bv 128)) => do
      v_4042 <- getRegister v_2442;
      v_4050 <- getRegister v_2443;
      setRegister (lhs.of_reg v_2443) (concat (concat (concat (add (extract v_4042 0 32) (extract v_4042 32 64)) (add (extract v_4042 64 96) (extract v_4042 96 128))) (add (extract v_4050 0 32) (extract v_4050 32 64))) (add (extract v_4050 64 96) (extract v_4050 96 128)));
      pure ()
    pat_end;
    pattern fun (v_2438 : Mem) (v_2439 : reg (bv 128)) => do
      v_11176 <- evaluateAddress v_2438;
      v_11177 <- load v_11176 16;
      v_11185 <- getRegister v_2439;
      setRegister (lhs.of_reg v_2439) (concat (concat (concat (add (extract v_11177 0 32) (extract v_11177 32 64)) (add (extract v_11177 64 96) (extract v_11177 96 128))) (add (extract v_11185 0 32) (extract v_11185 32 64))) (add (extract v_11185 64 96) (extract v_11185 96 128)));
      pure ()
    pat_end
