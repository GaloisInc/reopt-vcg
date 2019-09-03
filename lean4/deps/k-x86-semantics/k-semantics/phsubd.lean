def phsubd1 : instruction :=
  definst "phsubd" $ do
    pattern fun (v_2464 : reg (bv 128)) (v_2465 : reg (bv 128)) => do
      v_4235 <- getRegister v_2464;
      v_4243 <- getRegister v_2465;
      setRegister (lhs.of_reg v_2465) (concat (concat (concat (sub (extract v_4235 32 64) (extract v_4235 0 32)) (sub (extract v_4235 96 128) (extract v_4235 64 96))) (sub (extract v_4243 32 64) (extract v_4243 0 32))) (sub (extract v_4243 96 128) (extract v_4243 64 96)));
      pure ()
    pat_end;
    pattern fun (v_2459 : Mem) (v_2460 : reg (bv 128)) => do
      v_11687 <- evaluateAddress v_2459;
      v_11688 <- load v_11687 16;
      v_11696 <- getRegister v_2460;
      setRegister (lhs.of_reg v_2460) (concat (concat (concat (sub (extract v_11688 32 64) (extract v_11688 0 32)) (sub (extract v_11688 96 128) (extract v_11688 64 96))) (sub (extract v_11696 32 64) (extract v_11696 0 32))) (sub (extract v_11696 96 128) (extract v_11696 64 96)));
      pure ()
    pat_end
