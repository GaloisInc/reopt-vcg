def phaddd1 : instruction :=
  definst "phaddd" $ do
    pattern fun (v_2491 : reg (bv 128)) (v_2492 : reg (bv 128)) => do
      v_4093 <- getRegister v_2491;
      v_4101 <- getRegister v_2492;
      setRegister (lhs.of_reg v_2492) (concat (concat (concat (add (extract v_4093 0 32) (extract v_4093 32 64)) (add (extract v_4093 64 96) (extract v_4093 96 128))) (add (extract v_4101 0 32) (extract v_4101 32 64))) (add (extract v_4101 64 96) (extract v_4101 96 128)));
      pure ()
    pat_end;
    pattern fun (v_2488 : Mem) (v_2487 : reg (bv 128)) => do
      v_11053 <- evaluateAddress v_2488;
      v_11054 <- load v_11053 16;
      v_11062 <- getRegister v_2487;
      setRegister (lhs.of_reg v_2487) (concat (concat (concat (add (extract v_11054 0 32) (extract v_11054 32 64)) (add (extract v_11054 64 96) (extract v_11054 96 128))) (add (extract v_11062 0 32) (extract v_11062 32 64))) (add (extract v_11062 64 96) (extract v_11062 96 128)));
      pure ()
    pat_end
