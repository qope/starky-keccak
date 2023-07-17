use itertools::Itertools;
use tiny_keccak::keccakf;

pub fn keccak256_native(input: Vec<u32>) -> [u32; 8] {
    let block_size = 136 / 4;
    let num_blocks = input.len() / block_size + 1;
    let mut padded = vec![0u32; block_size * num_blocks];
    for i in 0..input.len() {
        padded[i] = input[i];
    }
    padded[input.len()] = 0x01;
    *padded.last_mut().unwrap() ^= 0x80 << 24;
    let mut state = [0u64; 25];
    for i in 0..num_blocks {
        for j in 0..block_size / 2 {
            state[j] ^= (padded[i * block_size + 2 * j] as u64)
                + ((padded[i * block_size + 2 * j + 1] as u64) << 32);
        }
        keccakf(&mut state);
    }
    let output = state[0..4]
        .iter()
        .flat_map(|&x| vec![x as u32, (x >> 32) as u32])
        .collect_vec();
    output.try_into().unwrap()
}

#[cfg(test)]
mod tests {
    use itertools::Itertools;
    use rand::Rng;
    use tiny_keccak::{Hasher, Keccak};

    use super::keccak256_native;

    #[test]
    fn test_keccak256() {
        let mut rng = rand::thread_rng();
        let input = vec![rng.gen(); 3153];
        let output = keccak256_native(input.clone());
        let output_expected: [u32; 8] = {
            let mut hasher = Keccak::v256();
            let mut output = [0u8; 32];
            let input = input
                .iter()
                .flat_map(|&x| vec![x as u8, (x >> 8) as u8, (x >> 16) as u8, (x >> 24) as u8])
                .collect_vec();
            hasher.update(&input);
            hasher.finalize(&mut output);
            let output = output
                .chunks(4)
                .map(|chunk| {
                    let mut res = 0u32;
                    for i in 0..4 {
                        res += (chunk[i] as u32) << (8 * i);
                    }
                    res
                })
                .collect_vec();
            output.try_into().unwrap()
        };

        assert!(output == output_expected);
    }
}
